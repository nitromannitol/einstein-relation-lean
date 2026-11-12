import EinsteinRelation.Correctors.ConditionalWeakEquation

/-! # Conditioning a local flux equation

Source: `paper/main.tex:913–925`. The coefficient matrix is observed by a
fixed conditioning sigma algebra throughout the spatial domain. These
lemmas derive the flux equation for joint conditional versions from the
original spatial weak equation and ordinary product integrability.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- Conditional averaging commutes with multiplication by an observed
coefficient matrix, spatially almost everywhere on one probability-one set.
Source: `paper/main.tex:919–925`. -/
theorem conditionalSpatialAverage_mulVec_ae_spatial {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (A : Ω → Vec d → Mat d) (g : Ω → Vec d → Vec d)
    (hAm : ∀ j k, Measurable (fun z : Ω × Vec d => A z.1 z.2 j k))
    (hgm : ∀ k, StronglyMeasurable (fun z : Ω × Vec d => g z.1 z.2 k))
    (hobs : ∀ j k, ∀ᵐ x ∂volume.restrict U,
      StronglyMeasurable[m] (fun a => A a x j k))
    (hAg : ∀ j k, Integrable (fun z : Ω × Vec d => A z.1 z.2 j k * g z.1 z.2 k)
      (μ.prod (volume.restrict U)))
    (hgi : ∀ k, Integrable (fun z : Ω × Vec d => g z.1 z.2 k)
      (μ.prod (volume.restrict U))) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂volume.restrict U,
      (fun j => conditionalSpatialAverage m μ
        (fun a y => ((A a y).mulVec (g a y)) j) ω x) =
        (A ω x).mulVec (fun k => conditionalSpatialAverage m μ
          (fun a y => g a y k) ω x) := by
  have hpull : ∀ᵐ ω ∂μ, ∀ j k : Fin d, ∀ᵐ x ∂volume.restrict U,
      conditionalSpatialAverage m μ (fun a y => A a y j k * g a y k) ω x =
        A ω x j k * conditionalSpatialAverage m μ (fun a y => g a y k) ω x :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      conditionalSpatialAverage_mul_ae_spatial m μ hm U
        (fun a y => A a y j k) (fun a y => g a y k)
        (hAm j k) (hgm k) (hobs j k) (hAg j k) (hgi k)
  have hprod : ∀ᵐ ω ∂μ, ∀ j k : Fin d,
      Integrable (fun z : Ω × Vec d => A z.1 z.2 j k * g z.1 z.2 k)
        ((condExpKernel μ m ω).prod (volume.restrict U)) :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      integrable_prod_condExpKernel_ae m μ hm (volume.restrict U) _
        ((hAm j k).mul (hgm k).measurable).stronglyMeasurable (hAg j k)
  filter_upwards [hpull, hprod] with ω hω hprodω
  have hsec : ∀ᵐ x ∂volume.restrict U, ∀ j k : Fin d,
      Integrable (fun a => A a x j k * g a x k) (condExpKernel μ m ω) :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => (hprodω j k).prod_left_ae
  have hpullx : ∀ᵐ x ∂volume.restrict U, ∀ j k : Fin d,
      conditionalSpatialAverage m μ (fun a y => A a y j k * g a y k) ω x =
        A ω x j k * conditionalSpatialAverage m μ (fun a y => g a y k) ω x :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hω j k
  filter_upwards [hsec, hpullx] with x hx hpx
  ext j
  change (∫ a, ∑ k : Fin d, A a x j k * g a x k ∂condExpKernel μ m ω) =
    ∑ k : Fin d, A ω x j k * conditionalSpatialAverage m μ (fun a y => g a y k) ω x
  rw [integral_finset_sum Finset.univ (fun k _ => hx j k)]
  exact Finset.sum_congr rfl fun k _ => hpx j k

/-- Subtracting a deterministic flux commutes with the same joint
conditional versions. Source: `paper/main.tex:919–925`. -/
theorem conditionalSpatialAverage_sub_const_ae_spatial {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) (f : Ω → Vec d → ℝ) (b : ℝ)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hfi : Integrable (Function.uncurry f) (μ.prod (volume.restrict U))) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂volume.restrict U,
      conditionalSpatialAverage m μ (fun a y => f a y - b) ω x =
        conditionalSpatialAverage m μ f ω x - b := by
  have hf := integrable_prod_condExpKernel_ae m μ hm (volume.restrict U)
    (Function.uncurry f) hfm hfi
  filter_upwards [hf] with ω hω
  filter_upwards [hω.prod_left_ae] with x hx
  change Integrable (fun a => f a x) (condExpKernel μ m ω) at hx
  simp only [conditionalSpatialAverage]
  rw [integral_sub hx (integrable_const b), integral_const]
  simp

/-- Conditioning preserves the local constitutive flux equation, with
one joint version for every matrix entry and flux coordinate. The original
equation is an ordinary spatial weak equation; no conditioned equation is
assumed. Source: `paper/main.tex:919–925`.

For the extended corrector, `g = eᵢ + ∇φᵢ` and `b = āeᵢ`. Identifying the
canonical fields and their Sobolev representatives is a separate step. -/
theorem hasWeakRowDivergence_conditional_flux {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (A : Ω → Vec d → Mat d) (g : Ω → Vec d → Vec d)
    (S : Ω → Vec d → Mat d) (b : Vec d)
    (hAm : ∀ j k, Measurable (fun z : Ω × Vec d => A z.1 z.2 j k))
    (hgm : ∀ k, StronglyMeasurable (fun z : Ω × Vec d => g z.1 z.2 k))
    (hSm : ∀ j k, StronglyMeasurable (fun z : Ω × Vec d => S z.1 z.2 j k))
    (hobs : ∀ j k, ∀ᵐ x ∂volume.restrict U,
      StronglyMeasurable[m] (fun a => A a x j k))
    (hAg : ∀ j k, Integrable (fun z : Ω × Vec d => A z.1 z.2 j k * g z.1 z.2 k)
      (μ.prod (volume.restrict U)))
    (hgi : ∀ k, Integrable (fun z : Ω × Vec d => g z.1 z.2 k)
      (μ.prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : Ω × Vec d => S z.1 z.2 j k)
      (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ a ∂μ, HasWeakRowDivergence U (S a)
      (fun x => (A a x).mulVec (g a x) - b)) :
    ∀ᵐ ω ∂μ, HasWeakRowDivergence U
      (fun x j k => conditionalSpatialAverage m μ (fun a y => S a y j k) ω x)
      (fun x => (A ω x).mulVec
        (fun k => conditionalSpatialAverage m μ (fun a y => g a y k) ω x) - b) := by
  have hfluxm (j : Fin d) : StronglyMeasurable
      (fun z : Ω × Vec d => ((A z.1 z.2).mulVec (g z.1 z.2)) j) := by
    exact Finset.stronglyMeasurable_fun_sum Finset.univ fun k _ =>
      ((hAm j k).mul (hgm k).measurable).stronglyMeasurable
  have hfluxi (j : Fin d) : Integrable
      (fun z : Ω × Vec d => ((A z.1 z.2).mulVec (g z.1 z.2)) j)
      (μ.prod (volume.restrict U)) :=
    integrable_finset_sum Finset.univ fun k _ => hAg j k
  have hrawm (j : Fin d) : StronglyMeasurable
      (fun z : Ω × Vec d => ((A z.1 z.2).mulVec (g z.1 z.2) - b) j) :=
    (hfluxm j).sub stronglyMeasurable_const
  have hrawi (j : Fin d) : Integrable
      (fun z : Ω × Vec d => ((A z.1 z.2).mulVec (g z.1 z.2) - b) j)
      (μ.prod (volume.restrict U)) :=
    (hfluxi j).sub (integrable_const (b j))
  have hw := hasWeakRowDivergence_conditionalSpatialAverage m μ hm U S
    (fun a y => (A a y).mulVec (g a y) - b) hSm hrawm hSi hrawi hweak
  have hpull := conditionalSpatialAverage_mulVec_ae_spatial m μ hm U A g
    hAm hgm hobs hAg hgi
  have hsub : ∀ᵐ ω ∂μ, ∀ j : Fin d, ∀ᵐ x ∂volume.restrict U,
      conditionalSpatialAverage m μ
          (fun a y => ((A a y).mulVec (g a y)) j - b j) ω x =
        conditionalSpatialAverage m μ
          (fun a y => ((A a y).mulVec (g a y)) j) ω x - b j :=
    ae_all_iff.mpr fun j => conditionalSpatialAverage_sub_const_ae_spatial m μ hm U
      (fun a y => ((A a y).mulVec (g a y)) j) (b j) (hfluxm j) (hfluxi j)
  have hrawfiber : ∀ᵐ ω ∂μ, ∀ j : Fin d, Integrable
      (fun z : Ω × Vec d => ((A z.1 z.2).mulVec (g z.1 z.2) - b) j)
      ((condExpKernel μ m ω).prod (volume.restrict U)) :=
    ae_all_iff.mpr fun j => integrable_prod_condExpKernel_ae m μ hm
      (volume.restrict U) _ (hrawm j) (hrawi j)
  filter_upwards [hw, hpull, hsub, hrawfiber] with ω hwω hpullω hsubω hrawω
  intro j
  have heq : (fun x => conditionalSpatialAverage m μ
      (fun a y => ((A a y).mulVec (g a y) - b) j) ω x) =ᵐ[volume.restrict U]
      (fun x => ((A ω x).mulVec
        (fun k => conditionalSpatialAverage m μ (fun a y => g a y k) ω x) - b) j) := by
    filter_upwards [hpullω, hsubω j] with x hx hsx
    exact hsx.trans (congrArg (fun v : Vec d => v j - b j) hx)
  have hint : IntegrableOn (fun x => conditionalSpatialAverage m μ
      (fun a y => ((A a y).mulVec (g a y) - b) j) ω x) U :=
    (hrawω j).integral_prod_right
  refine ⟨(hwω j).1, IntegrableOn.locallyIntegrableOn (hint.congr heq), ?_⟩
  intro ψ hψ
  rw [(hwω j).2.2 ψ hψ]
  congr 1
  exact integral_congr_ae (heq.mono fun x hx => congrArg (fun t => t * ψ x) hx)

/-- The scalar and matrix conditional versions satisfy the gradient and
constitutive flux equations together. This is the Sobolev conditioning step
for a fixed ball, before averaging over its centers.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakGradient_and_flux_conditional {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (A : Ω → Vec d → Mat d) (u : Ω → Vec d → ℝ)
    (G : Ω → Vec d → Vec d) (S : Ω → Vec d → Mat d) (e b : Vec d)
    (hAm : ∀ j k, Measurable (fun z : Ω × Vec d => A z.1 z.2 j k))
    (hum : StronglyMeasurable (Function.uncurry u))
    (hGm : ∀ k, StronglyMeasurable (fun z : Ω × Vec d => G z.1 z.2 k))
    (hSm : ∀ j k, StronglyMeasurable (fun z : Ω × Vec d => S z.1 z.2 j k))
    (hobs : ∀ j k, ∀ᵐ x ∂volume.restrict U,
      StronglyMeasurable[m] (fun a => A a x j k))
    (hAG : ∀ j k, Integrable (fun z : Ω × Vec d =>
      A z.1 z.2 j k * (e k + G z.1 z.2 k)) (μ.prod (volume.restrict U)))
    (hui : Integrable (Function.uncurry u) (μ.prod (volume.restrict U)))
    (hGi : ∀ k, Integrable (fun z : Ω × Vec d => G z.1 z.2 k)
      (μ.prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : Ω × Vec d => S z.1 z.2 j k)
      (μ.prod (volume.restrict U)))
    (hgrad : ∀ᵐ a ∂μ, HasWeakGradient U (u a) (G a))
    (hflux : ∀ᵐ a ∂μ, HasWeakRowDivergence U (S a)
      (fun x => (A a x).mulVec (e + G a x) - b)) :
    ∀ᵐ ω ∂μ,
      HasWeakGradient U (conditionalSpatialAverage m μ u ω)
        (fun x k => conditionalSpatialAverage m μ (fun a y => G a y k) ω x) ∧
      HasWeakRowDivergence U
        (fun x j k => conditionalSpatialAverage m μ (fun a y => S a y j k) ω x)
        (fun x => (A ω x).mulVec
          (e + fun k => conditionalSpatialAverage m μ (fun a y => G a y k) ω x) - b) := by
  have hg := hasWeakGradient_conditionalSpatialAverage m μ hm U u G
    hum hGm hui hGi hgrad
  have hf := hasWeakRowDivergence_conditional_flux m μ hm U A
    (fun a y => e + G a y) S b hAm
    (fun k => stronglyMeasurable_const.add (hGm k)) hSm hobs hAG
    (fun k => (integrable_const (e k)).add (hGi k)) hSi hflux
  have hshift : ∀ᵐ ω ∂μ, ∀ k : Fin d, ∀ᵐ x ∂volume.restrict U,
      conditionalSpatialAverage m μ (fun a y => e k + G a y k) ω x =
        e k + conditionalSpatialAverage m μ (fun a y => G a y k) ω x := by
    apply ae_all_iff.mpr
    intro k
    simpa only [sub_neg_eq_add, add_comm] using
      conditionalSpatialAverage_sub_const_ae_spatial m μ hm U
        (fun a y => G a y k) (-e k) (hGm k) (hGi k)
  filter_upwards [hg, hf, hshift] with ω hgω hfω hshiftω
  refine ⟨hgω, ?_⟩
  intro j
  have heq : (fun x => ((A ω x).mulVec
      (fun k => conditionalSpatialAverage m μ (fun a y => (e + G a y) k) ω x) - b) j)
      =ᵐ[volume.restrict U] (fun x => ((A ω x).mulVec
        (e + fun k => conditionalSpatialAverage m μ (fun a y => G a y k) ω x) - b) j) := by
    have hall := ae_all_iff.mpr hshiftω
    filter_upwards [hall] with x hx
    exact congrArg (fun v : Vec d => ((A ω x).mulVec v - b) j) (funext hx)
  have hlocal : LocallyIntegrableOn (fun x => ((A ω x).mulVec
      (e + fun k => conditionalSpatialAverage m μ (fun a y => G a y k) ω x) - b) j)
      U volume := by
    intro x hx
    obtain ⟨V, hV, hi⟩ := (hfω j).2.1 x hx
    refine ⟨V ∩ U, Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    exact (hi.mono_set Set.inter_subset_left).congr
      (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right heq)
  refine ⟨(hfω j).1, hlocal, ?_⟩
  intro ψ hψ
  rw [(hfω j).2.2 ψ hψ]
  congr 1
  exact integral_congr_ae (heq.mono fun x hx => congrArg (fun t => t * ψ x) hx)

end EinsteinRelation.Correctors
