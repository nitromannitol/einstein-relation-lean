import EinsteinFull.Calculus.CLDFGWCarrier
import EinsteinFull.External.Draft.DFGWInvarianceV2
import EinsteinFull.Calculus.CLCondExpPushforward
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
Transport of a process on an abstract carrier with continuous trajectories to its
trajectory space `C(ℝ, S)`, as the input `dfgwInvarianceStmtV2` requires. Not imported by
production.

The trajectory map `ω ↦ (t ↦ ξ t ω)` pulls the coordinate sigma-algebras back to those of the
process, intertwines the time shifts and reflections, and carries the law of the process to a
stationary, reversible, ergodic Markov law on trajectories with the same kernels.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.Draft

variable {Ω S : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace S] [SecondCountableTopology S]
  [RegularSpace S] [mS : MeasurableSpace S] [BorelSpace S]

/-- The trajectory of a process with continuous paths. -/
def trajOf (ξ : ℝ → Ω → S) (hcont : ∀ ω, Continuous fun t => ξ t ω) (ω : Ω) : C(ℝ, S) :=
  ⟨fun t => ξ t ω, hcont ω⟩

variable {ξ : ℝ → Ω → S} (hcont : ∀ ω, Continuous fun t => ξ t ω)

theorem measurable_trajOf (hξ : ∀ t, Measurable (ξ t)) : Measurable (trajOf ξ hcont) :=
  ContinuousMap.measurable_iff_eval.2 hξ

/-- For second countable regular `S` the Borel sigma-algebra of the trajectory space is the
coordinate sigma-algebra (the hypothesis of `dfgwInvarianceStmtV2` added after review v2). -/
theorem dfgwCoordSigma_univ_eq_borel :
    dfgwCoordSigma (S := S) Set.univ = dfgwTrajectoryMeasurableSpace (S := S) := by
  change _ = borel C(ℝ, S)
  rw [ContinuousMap.borel_eq_iSup_comap_eval]
  simp only [dfgwCoordSigma, Set.mem_univ, iSup_pos, BorelSpace.measurable_eq (α := S)]

omit [MeasurableSpace Ω] [SecondCountableTopology S] [RegularSpace S] [BorelSpace S] in
/-- The coordinate sigma-algebras of the trajectory space pull back to those of the process. -/
theorem comap_trajOf_coordSigma (I : Set ℝ) :
    MeasurableSpace.comap (trajOf ξ hcont) (dfgwCoordSigma I) = dfgwSigma ξ I := by
  simp only [dfgwCoordSigma, dfgwSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

omit [SecondCountableTopology S] [RegularSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem measurable_dfgwShift (τ : ℝ) : Measurable (dfgwShift (S := S) τ) :=
  (ContinuousMap.continuous_precomp _).measurable

omit [SecondCountableTopology S] [RegularSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem measurable_dfgwRefl (τ : ℝ) : Measurable (dfgwRefl (S := S) τ) :=
  (ContinuousMap.continuous_precomp _).measurable

omit [MeasurableSpace Ω] [SecondCountableTopology S] [RegularSpace S]
    [MeasurableSpace S] [BorelSpace S] in
theorem trajOf_shift {θ : ℝ → Ω → Ω} (hθ : ∀ τ t ω, ξ t (θ τ ω) = ξ (t + τ) ω) (τ : ℝ) :
    trajOf ξ hcont ∘ θ τ = dfgwShift τ ∘ trajOf ξ hcont := by
  funext ω
  ext t
  exact hθ τ t ω

omit [MeasurableSpace Ω] [SecondCountableTopology S] [RegularSpace S]
    [MeasurableSpace S] [BorelSpace S] in
theorem trajOf_refl {R : ℝ → Ω → Ω} (hR : ∀ τ t ω, ξ t (R τ ω) = ξ (2 * τ - t) ω) (τ : ℝ) :
    trajOf ξ hcont ∘ R τ = dfgwRefl τ ∘ trajOf ξ hcont := by
  funext ω
  ext t
  exact hR τ t ω

/-- The law of the process on its trajectory space is a stationary, reversible, ergodic Markov
law with the same invariant measure and kernels. -/
theorem isDFGWTrajectoryProcess_map {P : Measure Ω} {μ : Measure S} {θ R : ℝ → Ω → Ω}
    {T : ℝ≥0 → Kernel S S} (hproc : IsDFGWReversibleErgodicProcess P μ ξ θ R T) :
    IsDFGWTrajectoryProcess (P.map (trajOf ξ hcont)) μ T := by
  have hξ : ∀ t, Measurable (ξ t) := fun t =>
    hproc.measurable.comp ((measurable_const (a := t)).prodMk measurable_id)
  have htr := measurable_trajOf hcont hξ
  have := hproc.probability
  refine
    { probability := inferInstance
      invariant_probability := hproc.invariant_probability
      marginal := fun t => ?_
      stationary := fun τ => ?_
      reversible := fun τ => ?_
      markov_kernel := hproc.markov_kernel
      markov := fun t f hf hb => ?_
      ergodic := hproc.ergodic }
  · rw [Measure.map_map (continuous_eval_const t).measurable htr]
    exact hproc.marginal t
  · rw [Measure.map_map (measurable_dfgwShift τ) htr, ← trajOf_shift hcont hproc.translate,
      ← Measure.map_map htr (hproc.translate_measurable τ), hproc.stationary τ]
  · rw [Measure.map_map (measurable_dfgwRefl τ) htr, ← trajOf_refl hcont hproc.reflect,
      ← Measure.map_map htr (hproc.reflect_measurable τ), hproc.reversible τ]
  · obtain ⟨C, hC⟩ := hb
    have hfi : Integrable (fun η : C(ℝ, S) => f (η t)) (P.map (trajOf ξ hcont)) :=
      Integrable.of_bound ((hf.comp (continuous_eval_const _).measurable).aestronglyMeasurable)
        C (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hC (η t))
    have hle : dfgwCoordSigma (S := S) (Set.Iic 0) ≤ dfgwTrajectoryMeasurableSpace :=
      iSup₂_le fun u _ => (continuous_eval_const u).measurable.comap_le
    have hk : Measurable fun η : C(ℝ, S) => ∫ y, f y ∂T t (η 0) :=
      (StronglyMeasurable.integral_kernel (κ := T t) hf.stronglyMeasurable).measurable.comp
        (continuous_eval_const 0).measurable
    have h1 := condExp_map_comp htr hle hfi
    rw [comap_trajOf_coordSigma hcont] at h1
    have h2 := hproc.markov t f hf ⟨C, hC⟩
    have h3 : (fun ω => (P.map (trajOf ξ hcont))[fun η => f (η t) | dfgwCoordSigma (Set.Iic 0)]
        (trajOf ξ hcont ω)) =ᵐ[P] fun ω => (fun η : C(ℝ, S) => ∫ y, f y ∂T t (η 0))
          (trajOf ξ hcont ω) :=
      h1.trans h2
    refine (ae_map_iff htr.aemeasurable (measurableSet_eq_fun ?_ hk)).2 h3
    exact (stronglyMeasurable_condExp.mono hle).measurable

/-- The past coordinate sigma-algebra is the pullback of the Borel sigma-algebra of the restricted
trajectories. -/
theorem comap_restrict_Iic (t : ℝ) :
    MeasurableSpace.comap (fun η : C(ℝ, S) => η.restrict (Set.Iic t)) (borel C(Set.Iic t, S)) =
      dfgwCoordSigma (S := S) (Set.Iic t) := by
  haveI : LocallyCompactSpace (Set.Iic t) := isClosed_Iic.locallyCompactSpace
  rw [ContinuousMap.borel_eq_iSup_comap_eval, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, dfgwCoordSigma, ← BorelSpace.measurable_eq (α := S)]
  apply le_antisymm
  · exact iSup_le fun a => le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Iic t) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η s) mS) (a : ℝ) a.2 le_rfl
  · exact iSup₂_le fun s hs => le_iSup_of_le (⟨s, hs⟩ : Set.Iic t) le_rfl

/-- The time integral of a measurable function of the trajectory up to time `t` is measurable for
the past coordinate sigma-algebra. -/
theorem stronglyMeasurable_integral_past {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {φ : S → E} (hφ : Measurable φ) {t : ℝ} (ht : 0 ≤ t) :
    StronglyMeasurable[dfgwCoordSigma (S := S) (Set.Iic t)]
      fun η : C(ℝ, S) => ∫ τ in (0 : ℝ)..t, φ (η τ) := by
  haveI : LocallyCompactSpace (Set.Iic t) := isClosed_Iic.locallyCompactSpace
  borelize C(Set.Iic t, S)
  let e : ℝ → Set.Iic t := fun τ => ⟨min τ t, Set.mem_Iic.2 (min_le_right _ _)⟩
  have he : Continuous e := (continuous_id.min continuous_const).subtype_mk _
  let F : C(Set.Iic t, S) × ℝ → E := fun p => φ (p.1 (e p.2))
  have hF : StronglyMeasurable F :=
    (hφ.comp (continuous_eval.comp (continuous_fst.prodMk (he.comp continuous_snd))).measurable)
      |>.stronglyMeasurable
  have hH := hF.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
  have hres : Measurable[MeasurableSpace.comap (fun η : C(ℝ, S) => η.restrict (Set.Iic t))
      (borel C(Set.Iic t, S)), borel C(Set.Iic t, S)] fun η : C(ℝ, S) => η.restrict (Set.Iic t) :=
    comap_measurable _
  have hcomp := hH.comp_measurable hres
  rw [comap_restrict_Iic] at hcomp
  have heq : (fun η : C(ℝ, S) => ∫ τ in (0 : ℝ)..t, φ (η τ)) =
      (fun x => ∫ y in Set.Ioc (0 : ℝ) t, F (x, y)) ∘ fun η : C(ℝ, S) => η.restrict (Set.Iic t) := by
    funext η
    change ∫ τ in (0 : ℝ)..t, φ (η τ) = ∫ τ in Set.Ioc (0 : ℝ) t, φ ((η.restrict (Set.Iic t)) (e τ))
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    simp only [ContinuousMap.restrict_apply, e, min_eq_left hτ.2]
  rw [heq]
  exact hcomp

/-- Matrices with real entries form a second countable space. -/
instance (d : ℕ) : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

example (d : ℕ) : SecondCountableTopology (FieldPair d) := inferInstance

end EinsteinFull.External.Draft
