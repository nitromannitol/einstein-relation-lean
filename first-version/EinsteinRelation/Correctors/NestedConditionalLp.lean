import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Nested conditional expectations in finite moment norms

Source: `paper/main.tex:948–973`, Steps 2 and 3 of Proposition 5.3. Conditioning on a
larger coefficient observation changes the error by at most a factor two. The
comparison of two conditional means costs only one copy of the smaller observation
error. These results use the norm of the value space, so they apply to Euclidean
vectors and to matrices with the Frobenius norm through their Euclidean realization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

variable {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [StandardBorelSpace E] in
private theorem eLpNorm_kernel_average_le {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] {μ : Measure A} [SFinite μ] (κ : Kernel A B)
    [IsMarkovKernel κ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : A × B → E} (hg : StronglyMeasurable g) :
    eLpNorm (fun a => ∫ b, g (a, b) ∂κ a) p μ ≤ eLpNorm g p (μ ⊗ₘ κ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt]
  refine ENNReal.rpow_le_rpow ?_ (one_div_pos.mpr hpr).le
  rw [Measure.lintegral_compProd (hg.enorm.pow_const p.toReal)]
  refine lintegral_mono fun a => ?_
  have havg : ‖∫ b, g (a, b) ∂κ a‖ₑ ≤ eLpNorm (fun b => g (a, b)) p (κ a) := by
    calc
      ‖∫ b, g (a, b) ∂κ a‖ₑ ≤ ∫⁻ b, ‖g (a, b)‖ₑ ∂κ a :=
        enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun b => g (a, b)) 1 (κ a) := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm (fun b => g (a, b)) p (κ a) :=
        eLpNorm_le_eLpNorm_of_exponent_le hp
          (hg.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  calc
    ‖∫ b, g (a, b) ∂κ a‖ₑ ^ p.toReal ≤
        (eLpNorm (fun b => g (a, b)) p (κ a)) ^ p.toReal :=
      ENNReal.rpow_le_rpow havg hpr.le
    _ = ∫⁻ b, ‖g (a, b)‖ₑ ^ p.toReal ∂κ a := by
      rw [eLpNorm_eq_eLpNorm' hp0 hpt]
      exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr).symm

/-- Finite moment contraction for a measurable observation on a probability space.
Source: conditional Jensen in `paper/main.tex:948–973`. No regularity of the
sample space is needed; the conditional distribution takes values in `E`. -/
theorem eLpNorm_condExp_comap_le_normed {B : Type*} [mB : MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → B) (hX : Measurable X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : Ω → E} (hf : Integrable f μ) :
    eLpNorm (μ[f | mB.comap X]) p μ ≤ eLpNorm f p μ := by
  set κ : Kernel B E := condDistrib f X μ with hκ
  letI : IsMarkovKernel κ := inferInstanceAs (IsMarkovKernel (condDistrib f X μ))
  have hce : μ[f | mB.comap X] =ᵐ[μ] fun a => ∫ y, y ∂κ (X a) :=
    condExp_ae_eq_integral_condDistrib' hX hf
  have hmean : StronglyMeasurable (fun b => ∫ y : E, y ∂κ b) :=
    stronglyMeasurable_id.integral_kernel
  rw [eLpNorm_congr_ae hce]
  have hleft : eLpNorm (fun a => ∫ y : E, y ∂κ (X a)) p μ =
      eLpNorm (fun b => ∫ y : E, y ∂κ b) p (μ.map X) :=
    (eLpNorm_map_measure (μ := μ) (f := X) (g := fun b => ∫ y : E, y ∂κ b)
      (p := p) hmean.aestronglyMeasurable hX.aemeasurable).symm
  have hbound : eLpNorm (fun b => ∫ y : E, y ∂κ b) p (μ.map X) ≤
      eLpNorm (fun z : B × E => z.2) p ((μ.map X) ⊗ₘ κ) :=
    eLpNorm_kernel_average_le (E := E) (μ := μ.map X) (g := fun z : B × E => z.2)
      κ hp hpt measurable_snd.stronglyMeasurable
  have hright : eLpNorm (fun z : B × E => z.2) p ((μ.map X) ⊗ₘ κ) =
      eLpNorm f p μ := by
    rw [hκ, compProd_map_condDistrib hf.aestronglyMeasurable.aemeasurable]
    exact eLpNorm_map_measure (μ := μ) (f := fun a => (X a, f a))
      (g := fun z : B × E => z.2) (p := p) measurable_snd.aestronglyMeasurable
      (hX.aemeasurable.prodMk hf.aestronglyMeasurable.aemeasurable)
  exact hleft.le.trans (hbound.trans_eq hright)

/-- Comparing two nested conditional means costs only the error at the smaller
observation. Source: `paper/main.tex:956–961,968–973`. -/
theorem eLpNorm_condExp_comap_sub_condExp_le {B : Type*} [mB : MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → B) (hX : Measurable X)
    {m : MeasurableSpace Ω} (hm : m ≤ mB.comap X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : Ω → E} (hf : Integrable f μ) :
    eLpNorm (μ[f | mB.comap X] - μ[f | m]) p μ ≤ eLpNorm (f - μ[f | m]) p μ := by
  letI : MeasurableSpace Ω := m₀
  have hfix : μ[μ[f | m] | mB.comap X] = μ[f | m] :=
    condExp_of_stronglyMeasurable hX.comap_le
      (stronglyMeasurable_condExp.mono hm) integrable_condExp
  have heq : μ[f - μ[f | m] | mB.comap X] =ᵐ[μ]
      μ[f | mB.comap X] - μ[f | m] := by
    simpa only [hfix] using condExp_sub hf (integrable_condExp (f := f) (m := m))
      (mB.comap X)
  rw [← eLpNorm_congr_ae heq]
  exact eLpNorm_condExp_comap_le_normed X hX hp hpt (hf.sub integrable_condExp)

/-- The error after enlarging an observation is at most twice the old error.
Source: `paper/main.tex:959–961`. -/
theorem eLpNorm_sub_condExp_comap_le_two_mul {B : Type*} [mB : MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → B) (hX : Measurable X)
    {m : MeasurableSpace Ω} (hm : m ≤ mB.comap X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : Ω → E} (hf : Integrable f μ) :
    eLpNorm (f - μ[f | mB.comap X]) p μ ≤ 2 * eLpNorm (f - μ[f | m]) p μ := by
  letI : MeasurableSpace Ω := m₀
  have hm₀ : m ≤ m₀ := hm.trans hX.comap_le
  have hsmall : AEStronglyMeasurable (μ[f | m]) μ :=
    (stronglyMeasurable_condExp.mono hm₀).aestronglyMeasurable
  have hlarge : AEStronglyMeasurable (μ[f | mB.comap X]) μ :=
    (stronglyMeasurable_condExp.mono hX.comap_le).aestronglyMeasurable
  have heq : f - μ[f | mB.comap X] =
      (f - μ[f | m]) - (μ[f | mB.comap X] - μ[f | m]) := by
    ext ω
    simp only [Pi.sub_apply]
    abel
  calc
    eLpNorm (f - μ[f | mB.comap X]) p μ =
        eLpNorm ((f - μ[f | m]) - (μ[f | mB.comap X] - μ[f | m])) p μ := by rw [heq]
    _ ≤ eLpNorm (f - μ[f | m]) p μ +
        eLpNorm (μ[f | mB.comap X] - μ[f | m]) p μ :=
      eLpNorm_sub_le (hf.aestronglyMeasurable.sub hsmall) (hlarge.sub hsmall) hp
    _ ≤ eLpNorm (f - μ[f | m]) p μ + eLpNorm (f - μ[f | m]) p μ :=
      add_le_add le_rfl (eLpNorm_condExp_comap_sub_condExp_le X hX hm hp hpt hf)
    _ = 2 * eLpNorm (f - μ[f | m]) p μ := (two_mul _).symm

/-- Nested conditioning with a change of additive normalization. In dimension two
`f` is the centered corrector at the origin and `g` is the difference of its two
mollifier averages. Source: `paper/main.tex:953–961`. -/
theorem eLpNorm_condExp_comap_add_sub_condExp_le {B : Type*} [mB : MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → B) (hX : Measurable X)
    {m : MeasurableSpace Ω} (hm : m ≤ mB.comap X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f g : Ω → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    eLpNorm (μ[f + g | mB.comap X] - μ[f | m]) p μ ≤
      eLpNorm (f - μ[f | m]) p μ + eLpNorm g p μ := by
  letI : MeasurableSpace Ω := m₀
  have hsmall : AEStronglyMeasurable (μ[f | m]) μ :=
    (stronglyMeasurable_condExp.mono (hm.trans hX.comap_le)).aestronglyMeasurable
  have heq : μ[f + g | mB.comap X] - μ[f | m] =ᵐ[μ]
      (μ[f | mB.comap X] - μ[f | m]) + μ[g | mB.comap X] := by
    filter_upwards [condExp_add hf hg (mB.comap X)] with ω hω
    simp only [Pi.sub_apply, Pi.add_apply] at hω ⊢
    rw [hω]
    abel
  rw [eLpNorm_congr_ae heq]
  exact (eLpNorm_add_le
    ((stronglyMeasurable_condExp.mono hX.comap_le).aestronglyMeasurable.sub hsmall)
    (stronglyMeasurable_condExp.mono hX.comap_le).aestronglyMeasurable hp).trans
      (add_le_add (eLpNorm_condExp_comap_sub_condExp_le X hX hm hp hpt hf)
        (eLpNorm_condExp_comap_le_normed X hX hp hpt hg))

end EinsteinRelation.Correctors
