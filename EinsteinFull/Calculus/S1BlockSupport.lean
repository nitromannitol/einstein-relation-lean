import EinsteinFull.Calculus.S1LocalIntegralSupport
import EinsteinFull.Calculus.S1FiniteRangeSupport

/-! Spatial averages ("blocks") of a stationary, local, mean-zero random field that is
jointly measurable in `(x, ω)` only up to a null set. All statements are about the
actual Bochner integral `ω ↦ ∫ y in C, F y ω`; no measurable representative in `(y, ω)`
is used. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1
open EinsteinRelation

variable {d : ℕ}

/-- The properties of a localized covariance field used to build and compare blocks:
joint a.e.-measurability, square integrability, centering, `V x`-locality of each
value (up to a null set) and stationarity. -/
structure LocalStationaryField (μ : Measure (FieldPair d)) (V : Vec d → Set (Vec d))
    (F : Vec d → FieldPair d → ℝ) : Prop where
  meas : AEStronglyMeasurable (fun p : Vec d × FieldPair d => F p.1 p.2) (volume.prod μ)
  memLp : ∀ x, MemLp (F x) 2 μ
  mean_zero : ∀ x, ∫ ω, F x ω ∂μ = 0
  local_rep : ∀ x, ∃ g : FieldPair d → ℝ, Measurable[localSigma (V x)] g ∧ g =ᵐ[μ] F x
  stationary : ∀ x, F x =ᵐ[μ] fun ω => F 0 (translate x ω)

theorem integrable_prod_of_slice_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {G : Vec d → Ω → ℝ} {C : Set (Vec d)} (hC : volume C < ⊤)
    (hG : AEStronglyMeasurable (fun p : Vec d × Ω => G p.1 p.2) (volume.prod μ))
    (hint : ∀ y, Integrable (G y) μ) {K : ℝ} (hK : ∀ y, ∫ ω, ‖G y ω‖ ∂μ ≤ K) :
    Integrable (fun p : Vec d × Ω => G p.1 p.2) ((volume.restrict C).prod μ) := by
  haveI : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC⟩
  have hG' : AEStronglyMeasurable (fun p : Vec d × Ω => G p.1 p.2)
      ((volume.restrict C).prod μ) :=
    hG.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  refine (integrable_prod_iff hG').2 ⟨Filter.Eventually.of_forall hint, ?_⟩
  have hm : AEStronglyMeasurable (fun y => ∫ ω, ‖G y ω‖ ∂μ) (volume.restrict C) :=
    (hG.norm.integral_prod_right').mono_measure Measure.restrict_le_self
  refine Integrable.mono' (integrable_const K) hm (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  exact hK y

section Field

variable {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] {V : Vec d → Set (Vec d)}
  {F : Vec d → FieldPair d → ℝ}

omit [IsProbabilityMeasure μ] in
theorem LocalStationaryField.integral_norm_eq (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) (x : Vec d) :
    ∫ ω, ‖F x ω‖ ∂μ = ∫ ω, ‖F 0 ω‖ ∂μ := by
  have h0 : AEStronglyMeasurable (fun ω => ‖F 0 ω‖) μ := (h.memLp 0).aestronglyMeasurable.norm
  have hm := integral_map (μ := μ) (EinsteinRelation.Probability.measurable_translate x).aemeasurable
    (f := fun ω => ‖F 0 ω‖) (by rw [(hT x).map_eq]; exact h0)
  rw [(hT x).map_eq] at hm
  calc ∫ ω, ‖F x ω‖ ∂μ = ∫ ω, ‖F 0 (translate x ω)‖ ∂μ :=
        integral_congr_ae ((h.stationary x).mono fun ω hω => by simp only [hω])
    _ = ∫ ω, ‖F 0 ω‖ ∂μ := hm.symm

theorem LocalStationaryField.integrable_prod (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) {C : Set (Vec d)} (hC : volume C < ⊤) :
    Integrable (fun p : Vec d × FieldPair d => F p.1 p.2) ((volume.restrict C).prod μ) :=
  integrable_prod_of_slice_bound hC h.meas (fun y => (h.memLp y).integrable one_le_two)
    (K := ∫ ω, ‖F 0 ω‖ ∂μ) (fun y => (h.integral_norm_eq hT y).le)

theorem LocalStationaryField.ae_integrable_slice (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) {C : Set (Vec d)} (hC : volume C < ⊤) :
    ∀ᵐ ω ∂μ, Integrable (fun y => F y ω) (volume.restrict C) :=
  (h.integrable_prod hT hC).prod_left_ae

theorem LocalStationaryField.integrable_block (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) {C : Set (Vec d)} (hC : volume C < ⊤) :
    Integrable (fun ω => ∫ y in C, F y ω) μ :=
  (h.integrable_prod hT hC).integral_prod_right

theorem LocalStationaryField.integral_block (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) {C : Set (Vec d)} (hC : volume C < ⊤) :
    ∫ ω, (∫ y in C, F y ω) ∂μ = 0 := by
  haveI : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC⟩
  have hint := h.integrable_prod hT hC
  have hsw := integral_integral_swap (μ := μ) (ν := volume.restrict C)
    (f := fun ω y => F y ω) hint.swap
  rw [hsw]
  have : ∀ y, ∫ ω, F y ω ∂μ = 0 := h.mean_zero
  simp only [this, integral_zero]

theorem LocalStationaryField.block_local (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (h : LocalStationaryField μ V F) {C : Set (Vec d)} (hCm : MeasurableSet C)
    (hC : volume C < ⊤) {U : Set (Vec d)} (hCV : ∀ y ∈ C, V y ⊆ U) :
    ∃ H : FieldPair d → ℝ, StronglyMeasurable[localSigma U] H ∧
      (fun ω => ∫ y in C, F y ω) =ᵐ[μ] H := by
  haveI : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC⟩
  refine local_integral_aeEq_measurable (ν := volume.restrict C)
    (F := fun p : Vec d × FieldPair d => F p.1 p.2)
    (EinsteinRelation.Probability.localSigma_le_borel U) (h.integrable_prod hT hC) ?_
  refine (ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall fun y hy => ?_)
  obtain ⟨g, hgm, hg⟩ := h.local_rep y
  exact ⟨g, (hgm.mono (localSigma_mono (hCV y hy)) le_rfl).stronglyMeasurable, hg.symm⟩

end Field

/-- Two jointly integrable families whose slices agree a.e. have a.e.-equal
`y`-integrals; no product-measurable null set is needed. -/
theorem integral_aeEq_of_slice_aeEq {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Y} [SFinite ν]
    {F1 F2 : Y × Ω → ℝ} (h1 : Integrable F1 (ν.prod μ)) (h2 : Integrable F2 (ν.prod μ))
    (h : ∀ᵐ y ∂ν, (fun ω => F1 (y, ω)) =ᵐ[μ] fun ω => F2 (y, ω)) :
    (fun ω => ∫ y, F1 (y, ω) ∂ν) =ᵐ[μ] fun ω => ∫ y, F2 (y, ω) ∂ν := by
  have hD := h1.sub h2
  have hH : Integrable (fun ω => ∫ y, (F1 - F2) (y, ω) ∂ν) μ := hD.integral_prod_right
  have hzero : (fun ω => ∫ y, (F1 - F2) (y, ω) ∂ν) =ᵐ[μ] 0 := by
    refine hH.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => ?_
    have hDs : Integrable (F1 - F2) (ν.prod (μ.restrict s)) :=
      hD.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hsw := integral_integral_swap (μ := μ.restrict s) (ν := ν)
      (f := fun ω y => (F1 - F2) (y, ω)) hDs.swap
    rw [hsw]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with y hy
    have : (fun ω => (F1 - F2) (y, ω)) =ᵐ[μ.restrict s] 0 :=
      ae_restrict_of_ae (hy.mono fun ω hω => by simp [Pi.sub_apply, hω])
    show ∫ ω in s, (F1 - F2) (y, ω) ∂μ = 0
    rw [integral_congr_ae this]
    simp
  filter_upwards [hzero, h1.prod_left_ae, h2.prod_left_ae] with ω hω hs1 hs2
  have e : ∫ y, (F1 - F2) (y, ω) ∂ν = (∫ y, F1 (y, ω) ∂ν) - ∫ y, F2 (y, ω) ∂ν :=
    integral_sub hs1 hs2
  have : (∫ y, F1 (y, ω) ∂ν) - ∫ y, F2 (y, ω) ∂ν = 0 := by
    rw [← e]
    exact hω
  exact sub_eq_zero.mp this

end EinsteinFull.Calculus.S1
