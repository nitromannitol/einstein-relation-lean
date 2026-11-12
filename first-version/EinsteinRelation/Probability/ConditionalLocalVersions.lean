import EinsteinRelation.Probability.LocalKernelVersion
import EinsteinRelation.Probability.ReductionInverseLocality
import EinsteinRelation.Environment.ReductionImageSupport
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Local versions by conditional resampling of the actual environment

Source `paper/main.tex:383–387`. Resampling an environment conditional on
its local sigma-algebra preserves all observations in that region. The
simultaneous statement uses continuity of the actual fields and a
countable dense set. Scalar functions constant under this resampling
therefore have local measurable versions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Probability

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- Conditional resampling preserves every observation measurable for
the conditioning sigma-algebra. -/
theorem ae_condExpKernel_observation_eq {α E : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    (X : α → E) (hX : Measurable[m] X) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, X a = X b := by
  letI : MeasurableSpace α := mα
  letI : MeasurableSpace (α × α) := m.prod mα
  have hp : @MeasurableSet (α × α) (m.prod mα) {p | X p.1 = X p.2} :=
    measurableSet_eq_fun (hX.comp (@measurable_fst α α m mα))
      ((hX.mono hm le_rfl).comp (@measurable_snd α α m mα))
  have hd : @Measurable α (α × α) mα (m.prod mα) (fun a => (a, a)) :=
    (measurable_id.mono le_rfl hm).prodMk measurable_id
  have hprod : ∀ᵐ p ∂(μ.trim hm).compProd (condExpKernel μ m), X p.1 = X p.2 := by
    rw [compProd_trim_condExpKernel hm]
    exact (ae_map_iff hd.aemeasurable hp).mpr (Filter.Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hprod)

/-- Conditional resampling preserves every event of full original
measure, including events not measurable for the local sigma-algebra. -/
theorem ae_condExpKernel_of_ae {α : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    {p : α → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, p b := by
  letI : MeasurableSpace α := mα
  have hcomp : ∀ᵐ b ∂condExpKernel μ m ∘ₘ μ.trim hm, p b := by
    rw [condExpKernel_comp_trim hm]
    exact hp
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hcomp)

/-- Conditional copies of continuous physical environments agree
simultaneously at every point of the conditioning region. -/
theorem ae_condExpKernel_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d)) :
    ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y := by
  letI : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  obtain ⟨A, hAc, hAd⟩ := TopologicalSpace.exists_countable_dense U
  haveI : Countable A := hAc.to_subtype
  have hpoints : ∀ a : A, ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      (ω.1 (a : U), ω.2 (a : U)) = (ω'.1 (a : U), ω'.2 (a : U)) := by
    intro a
    exact ae_condExpKernel_observation_eq Q (localSigma U) (localSigma_le_borel U)
      (fun ω : FieldPair d => (ω.1 (a : U), ω.2 (a : U)))
      (Measurable.of_comap_le (le_iSup
        (fun y : U => MeasurableSpace.comap
          (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) (a : U)))
  filter_upwards [ae_all_iff.mpr hpoints] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with ω' hω'
  have hfun : (fun y : U => (ω.1 y, ω.2 y)) = fun y : U => (ω'.1 y, ω'.2 y) := by
    apply Continuous.ext_on hAd
      ((ω.1.continuous.comp continuous_subtype_val).prodMk
        (ω.2.continuous.comp continuous_subtype_val))
      ((ω'.1.continuous.comp continuous_subtype_val).prodMk
        (ω'.2.continuous.comp continuous_subtype_val))
    intro a ha
    exact hω' ⟨a, ha⟩
  intro y hy
  exact Prod.mk.inj (congrFun hfun ⟨y, hy⟩)

/-- A measurable function unchanged by conditional resampling
has a measurable version for the conditioning sigma-algebra. -/
theorem exists_local_version_of_resampling_eq {α : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α)
    (f : α → ℝ) (hf : @Measurable α ℝ mα inferInstance f)
    (heq : ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, f a = f b) :
    ∃ A : α → ℝ, Measurable[m] A ∧ A =ᵐ[μ] f := by
  letI : MeasurableSpace α := mα
  refine ⟨fun a => ∫ b, f b ∂condExpKernel μ m a,
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  filter_upwards [heq] with a ha
  calc
    _ = ∫ _b, f a ∂condExpKernel μ m a :=
      integral_congr_ae (ha.mono fun _ h => h.symm)
    _ = f a := by simp

/-- A measurable field functional whose value depends only on the actual
coefficients on `U`, outside a full-measure set, has a local version. -/
theorem exists_local_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d))
    (f : FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (FieldPair d)) (hG : ∀ᵐ ω ∂Q, ω ∈ G)
    (hlocal : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → f ω = f ω') :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma U] A ∧ A =ᵐ[Q] f := by
  apply exists_local_version_of_resampling_eq Q (localSigma U) f hf
  filter_upwards [hG, ae_condExpKernel_of_ae Q (localSigma U) (localSigma_le_borel U) hG,
    ae_condExpKernel_fields_eq_on Q U] with ω hω hgood heq
  filter_upwards [hgood, heq] with ω' hω' heq'
  exact hlocal ω hω ω' hω' heq'


end EinsteinRelation.Probability
