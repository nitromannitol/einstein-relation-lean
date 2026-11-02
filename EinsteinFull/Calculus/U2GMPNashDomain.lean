import EinsteinFull.Calculus.U1GMPKernelL2
import EinsteinFull.Calculus.U4PhysicalWeightedNash

open EinsteinRelation MeasureTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- The unforced physical measure has the same Lᵖ functions as volume. -/
theorem u2_unforced_physical_memLp_iff_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (p : ℝ≥0∞) (f : Vec d → ℝ) :
    MemLp f p (physicalReversibleMeasure ω hd 0) ↔ MemLp f p volume := by
  have hcmp := u4_unforced_physical_measure_comparable hd ω Λ hω
  constructor
  · intro hf
    exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hcmp.2
  · intro hf
    exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hcmp.1

/-- Indicators of finite-volume measurable sets belong to the actual physical L² space. -/
theorem u2_unforced_physical_indicator_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω) {A : Set (Vec d)}
    (hA : MeasurableSet A) (hfinite : (volume : Measure (Vec d)) A < ∞) :
    MemLp (A.indicator (fun _ => (1 : ℝ))) 2 (physicalReversibleMeasure ω hd 0) := by
  have hphys : physicalReversibleMeasure ω hd 0 A < ∞ := by
    calc
      physicalReversibleMeasure ω hd 0 A ≤
          (ENNReal.ofReal (Real.exp (2 * Λ)) • (volume : Measure (Vec d))) A :=
        (u4_unforced_physical_measure_comparable hd ω Λ hω).1 A
      _ = ENNReal.ofReal (Real.exp (2 * Λ)) * (volume : Measure (Vec d)) A := by simp
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
  exact memLp_indicator_const 2 hA (1 : ℝ) (Or.inr hphys.ne)

/-- Kernel integration is additive on the actual unforced L² domain almost everywhere. -/
theorem u2_unforced_physical_kernel_integral_add_ae
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f g : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd 0))
    (hg : MemLp g 2 (physicalReversibleMeasure ω hd 0)) :
    (fun x => ∫ y, (f y + g y) ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) +
      ∫ y, g y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) := by
  apply (Measure.absolutelyContinuous_of_le_smul
    (u4_unforced_physical_measure_comparable hd ω Λ hω).2).ae_eq
  filter_upwards [(u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
    hd ω 0 Λ hΛ hω hSmooth t f hf).1,
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
    hd ω 0 Λ hΛ hω hSmooth t g hg).1] with x hfi hgi
  exact integral_add hfi hgi

/-- Scalar multiplication commutes with integration against each actual kernel. -/
theorem u2_unforced_physical_kernel_integral_smul
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f : Vec d → ℝ) (c : ℝ) (x : Vec d) :
    (∫ y, c * f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x) =
      c * ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x := by
  exact integral_const_mul c f

/-- The actual kernel preserves pointwise nonnegativity. -/
theorem u2_unforced_physical_kernel_integral_nonneg
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f : Vec d → ℝ) (hf : ∀ y, 0 ≤ f y) (x : Vec d) :
    0 ≤ ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x := by
  exact integral_nonneg hf

/-- Kernel outputs of physical L² inputs are Lebesgue almost-everywhere measurable. -/
theorem u2_unforced_physical_kernel_integral_aemeasurable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd 0)) :
    AEMeasurable (fun x => ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) volume := by
  have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
    Measure.absolutelyContinuous_of_le_smul
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  have hm := (Lp.memLp (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
    (hf.toLp f))).aestronglyMeasurable.mono_ac hac
  exact (hm.congr (hac.ae_eq (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
    hd ω 0 Λ hΛ hω hSmooth t f hf).2).symm).aemeasurable

/-- Finite sums commute almost everywhere with the actual unforced kernel. -/
theorem u2_unforced_physical_kernel_integral_sum_ae
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → Vec d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (physicalReversibleMeasure ω hd 0)) :
    (fun x => ∫ y, (∑ i ∈ S, f i) y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) =ᵐ[volume]
    (fun x => ∑ i ∈ S, ∫ y, f i y ∂Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hS : MemLp (∑ j ∈ S, f j) 2 (physicalReversibleMeasure ω hd 0) :=
      memLp_finsetSum' S fun j _ => hf j
    filter_upwards [u2_unforced_physical_kernel_integral_add_ae
      hd ω Λ hΛ hω hSmooth t (f i) (∑ j ∈ S, f j) (hf i) hS, ih] with x ha hb
    simpa only [Pi.add_apply] using ha.trans (congrArg (fun z => _ + z) hb)


end EinsteinFull
