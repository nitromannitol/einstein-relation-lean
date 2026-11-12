import EinsteinRelation.Correctors.WeakEquationAveraging
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Joint conditional versions of spatial weak equations

Source: `paper/main.tex:913–925`. The conditioning sigma algebra is fixed
while the spatial argument varies. A single regular conditional probability
kernel supplies the joint versions, and Fubini preserves the actual spatial
weak equations. No uniqueness or regularity of a corrector is assumed here.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- The spatial field averaged against a single regular conditional law.
Source: `paper/main.tex:913–925`. The observation sigma algebra does not
depend on the spatial argument. -/
noncomputable def conditionalSpatialAverage {Ω : Type*} (m : MeasurableSpace Ω)
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : ℕ} (u : Ω → Vec d → ℝ) : Ω → Vec d → ℝ :=
  fun ω x => ∫ a, u a x ∂condExpKernel μ m ω

/-- The conditional spatial average is jointly measurable for the
observation sigma algebra and the spatial Borel sigma algebra.
Source: `paper/main.tex:913–925`. -/
theorem stronglyMeasurable_conditionalSpatialAverage {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : ℕ} (u : Ω → Vec d → ℝ)
    (hu : StronglyMeasurable (Function.uncurry u)) :
    StronglyMeasurable[m.prod (inferInstance : MeasurableSpace (Vec d))]
      (Function.uncurry (conditionalSpatialAverage m μ u)) := by
  let K := (condExpKernel μ m).prodMkRight (Vec d)
  have htest : StronglyMeasurable[
      (m.prod (inferInstance : MeasurableSpace (Vec d))).prod mΩ]
      (fun z : (Ω × Vec d) × Ω => u z.2 z.1.2) :=
    hu.comp_measurable (measurable_snd.prodMk measurable_fst.snd)
  exact htest.integral_kernel_prod_right' (κ := K)

/-- At each spatial point with an integrable section, the joint version
agrees almost surely with conditional expectation.
Source: `paper/main.tex:913–925`. -/
theorem conditionalSpatialAverage_ae_eq_condExp {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (u : Ω → Vec d → ℝ) (x : Vec d) (hu : Integrable (fun a => u a x) μ) :
    (fun ω => conditionalSpatialAverage m μ u ω x) =ᵐ[μ]
      μ[fun a => u a x | m] :=
  (condExp_ae_eq_integral_condExpKernel hm hu).symm

/-- An almost sure property holds in almost every conditional fiber.
Source: `paper/main.tex:913–925`. No measurability of the property itself
is needed: the almost sure hypothesis supplies a measurable null envelope. -/
theorem ae_condExpKernel_of_ae {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {p : Ω → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ ω ∂μ, ∀ᵐ a ∂condExpKernel μ m ω, p a := by
  apply ae_of_ae_trim hm
  apply Measure.ae_ae_of_ae_comp
  simpa only [condExpKernel_comp_trim hm] using hp

/-- Joint spatial integrability passes to almost every conditional fiber.
Source: `paper/main.tex:913–925`. This derives the fiber product bound from
the original field's product bound, rather than assuming it separately. -/
theorem integrable_prod_condExpKernel_ae {Ω X : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    (ν : Measure X) [SFinite ν] (f : Ω × X → ℝ)
    (hfm : StronglyMeasurable f) (hfi : Integrable f (μ.prod ν)) :
    ∀ᵐ ω ∂μ, Integrable f ((condExpKernel μ m ω).prod ν) := by
  have hsec := ae_condExpKernel_of_ae m μ hm hfi.prod_right_ae
  have hnorm := hfi.integral_norm_prod_left.condExpKernel_ae (m := m)
  filter_upwards [hsec, hnorm] with ω hω hnormω
  exact (integrable_prod_iff hfm.aestronglyMeasurable).mpr ⟨hω, hnormω⟩

/-- A joint conditional version of a weak gradient, obtained from the
actual weak equations and product integrability of the original fields.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakGradient_conditionalSpatialAverage {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (u : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hGm : ∀ j, StronglyMeasurable (fun z : Ω × Vec d => G z.1 z.2 j))
    (hui : Integrable (Function.uncurry u) (μ.prod (volume.restrict U)))
    (hGi : ∀ j, Integrable (fun z : Ω × Vec d => G z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ a ∂μ, HasWeakGradient U (u a) (G a)) :
    ∀ᵐ ω ∂μ, HasWeakGradient U (conditionalSpatialAverage m μ u ω)
      (fun x j => conditionalSpatialAverage m μ (fun a y => G a y j) ω x) := by
  have hu := integrable_prod_condExpKernel_ae m μ hm (volume.restrict U) _ hum hui
  have hG : ∀ᵐ ω ∂μ, ∀ j : Fin d,
      Integrable (fun z : Ω × Vec d => G z.1 z.2 j)
        ((condExpKernel μ m ω).prod (volume.restrict U)) :=
    ae_all_iff.mpr fun j =>
      integrable_prod_condExpKernel_ae m μ hm (volume.restrict U) _ (hGm j) (hGi j)
  have hw := ae_condExpKernel_of_ae m μ hm hweak
  filter_upwards [hu, hG, hw] with ω huω hGω hwω
  exact hasWeakGradient_integral (condExpKernel μ m ω) U u G huω hGω hwω

/-- Conditional expectation preserves the actual spatial weak divergence
equation with jointly measurable versions.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakDivergence_conditionalSpatialAverage {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (F : Ω → Vec d → Vec d) (h : Ω → Vec d → ℝ)
    (hFm : ∀ j, StronglyMeasurable (fun z : Ω × Vec d => F z.1 z.2 j))
    (hhm : StronglyMeasurable (Function.uncurry h))
    (hFi : ∀ j, Integrable (fun z : Ω × Vec d => F z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hhi : Integrable (Function.uncurry h) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ a ∂μ, HasWeakDivergence U (F a) (h a)) :
    ∀ᵐ ω ∂μ, HasWeakDivergence U
      (fun x j => conditionalSpatialAverage m μ (fun a y => F a y j) ω x)
      (conditionalSpatialAverage m μ h ω) := by
  have hF : ∀ᵐ ω ∂μ, ∀ j : Fin d,
      Integrable (fun z : Ω × Vec d => F z.1 z.2 j)
        ((condExpKernel μ m ω).prod (volume.restrict U)) :=
    ae_all_iff.mpr fun j =>
      integrable_prod_condExpKernel_ae m μ hm (volume.restrict U) _ (hFm j) (hFi j)
  have hh := integrable_prod_condExpKernel_ae m μ hm (volume.restrict U) _ hhm hhi
  have hw := ae_condExpKernel_of_ae m μ hm hweak
  filter_upwards [hF, hh, hw] with ω hFω hhω hwω
  exact hasWeakDivergence_integral (condExpKernel μ m ω) U F h hFω hhω hwω

/-- A matrix row-divergence equation holds for the same joint conditional
versions of all entries. Source: `paper/main.tex:913–925`. -/
theorem hasWeakRowDivergence_conditionalSpatialAverage {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (S : Ω → Vec d → Mat d) (h : Ω → Vec d → Vec d)
    (hSm : ∀ j k, StronglyMeasurable (fun z : Ω × Vec d => S z.1 z.2 j k))
    (hhm : ∀ j, StronglyMeasurable (fun z : Ω × Vec d => h z.1 z.2 j))
    (hSi : ∀ j k, Integrable (fun z : Ω × Vec d => S z.1 z.2 j k)
      (μ.prod (volume.restrict U)))
    (hhi : ∀ j, Integrable (fun z : Ω × Vec d => h z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ a ∂μ, HasWeakRowDivergence U (S a) (h a)) :
    ∀ᵐ ω ∂μ, HasWeakRowDivergence U
      (fun x j k => conditionalSpatialAverage m μ (fun a y => S a y j k) ω x)
      (fun x j => conditionalSpatialAverage m μ (fun a y => h a y j) ω x) := by
  apply ae_all_iff.mpr
  intro j
  exact hasWeakDivergence_conditionalSpatialAverage m μ hm U
    (fun a x k => S a x j k) (fun a x => h a x j)
    (hSm j) (hhm j) (hSi j) (hhi j) (hweak.mono fun _ ha => ha j)

/-- Averaging a genuinely skew-valued matrix field preserves skew symmetry
at every parameter, including exceptional conditional fibers.
Source: `paper/main.tex:913–925`. -/
theorem conditionalSpatialAverage_skew {Ω : Type*}
    (m : MeasurableSpace Ω) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {d : ℕ} (S : Ω → Vec d → Mat d)
    (hS : ∀ a x, (S a x).transpose = -(S a x)) (ω : Ω) (x : Vec d) :
    Matrix.transpose (fun j k => conditionalSpatialAverage m μ (fun a y => S a y j k) ω x) =
      -(fun j k => conditionalSpatialAverage m μ (fun a y => S a y j k) ω x) := by
  ext j k
  change (∫ a, S a x k j ∂condExpKernel μ m ω) =
    -(∫ a, S a x j k ∂condExpKernel μ m ω)
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => congrFun (congrFun (hS a x) j) k

/-- The observed coefficient can be pulled out of the joint conditional
average. In the local flux equation this is applied to each matrix entry
of `a(x)`, which is measurable for the fixed conditioning ball when `x`
lies in that ball. Source: `paper/main.tex:919–925`. -/
theorem conditionalSpatialAverage_mul_ae {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (f g : Ω → Vec d → ℝ) (x : Vec d)
    (hfm : StronglyMeasurable[m] (fun a => f a x))
    (hfg : Integrable (fun a => f a x * g a x) μ)
    (hg : Integrable (fun a => g a x) μ) :
    (fun ω => conditionalSpatialAverage m μ (fun a y => f a y * g a y) ω x) =ᵐ[μ]
      (fun ω => f ω x * conditionalSpatialAverage m μ g ω x) := by
  have hprod := conditionalSpatialAverage_ae_eq_condExp m μ hm
    (fun a y => f a y * g a y) x hfg
  have hmean := conditionalSpatialAverage_ae_eq_condExp m μ hm g x hg
  have hpull := condExp_mul_of_stronglyMeasurable_left hfm hfg hg
  filter_upwards [hprod, hmean, hpull] with ω hprodω hmeanω hpullω
  exact hprodω.trans (hpullω.trans (congrArg (fun t => f ω x * t) hmeanω.symm))

/-- The coefficient pull-out identity holds spatially almost everywhere on
one probability-one set, so it can be substituted in a spatial weak equation.
Source: `paper/main.tex:919–925`. -/
theorem conditionalSpatialAverage_mul_ae_spatial {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (f g : Ω → Vec d → ℝ)
    (hfm : Measurable (Function.uncurry f))
    (hgm : StronglyMeasurable (Function.uncurry g))
    (hfobs : ∀ᵐ x ∂volume.restrict U, StronglyMeasurable[m] (fun a => f a x))
    (hfg : Integrable (fun z : Ω × Vec d => f z.1 z.2 * g z.1 z.2)
      (μ.prod (volume.restrict U)))
    (hg : Integrable (Function.uncurry g) (μ.prod (volume.restrict U))) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂volume.restrict U,
      conditionalSpatialAverage m μ (fun a y => f a y * g a y) ω x =
        f ω x * conditionalSpatialAverage m μ g ω x := by
  have hpoint : ∀ᵐ x ∂volume.restrict U, ∀ᵐ ω ∂μ,
      conditionalSpatialAverage m μ (fun a y => f a y * g a y) ω x =
        f ω x * conditionalSpatialAverage m μ g ω x := by
    filter_upwards [hfobs, hfg.prod_left_ae, hg.prod_left_ae] with x hfx hfgx hgx
    exact conditionalSpatialAverage_mul_ae m μ hm f g x hfx hfgx hgx
  have hid : @Measurable (Ω × Vec d) (Ω × Vec d)
      (mΩ.prod inferInstance) (m.prod inferInstance) id :=
    ((measurable_id'' hm).comp measurable_fst).prodMk measurable_snd
  have hleft : StronglyMeasurable
      (Function.uncurry (conditionalSpatialAverage m μ (fun a y => f a y * g a y))) :=
    (stronglyMeasurable_conditionalSpatialAverage m μ _
      (hfm.mul hgm.measurable).stronglyMeasurable).comp_measurable hid
  have hright : StronglyMeasurable (Function.uncurry (conditionalSpatialAverage m μ g)) :=
    (stronglyMeasurable_conditionalSpatialAverage m μ g hgm).comp_measurable hid
  have heq : MeasurableSet {z : Ω × Vec d |
      conditionalSpatialAverage m μ (fun a y => f a y * g a y) z.1 z.2 =
        f z.1 z.2 * conditionalSpatialAverage m μ g z.1 z.2} :=
    measurableSet_eq_fun hleft.measurable (hfm.mul hright.measurable)
  exact (Measure.ae_ae_comm heq).mpr hpoint

end EinsteinRelation.Correctors
