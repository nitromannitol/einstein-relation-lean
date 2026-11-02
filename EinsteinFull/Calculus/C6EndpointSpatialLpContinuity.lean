import EinsteinFull.Calculus.C6EndpointFinitePContinuity
import EinsteinFull.Calculus.ComplexTranslationSupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
theorem endpoint_translate_tendsto_eLpNorm_sub_zero
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (ν : EndpointIndex d) (t : ℝ≥0) :
    Tendsto (fun x : Vec d =>
      eLpNorm (fun ω : FieldPair d =>
        (indexedEndpoint hd Q ν ζ P T β a μ t) (translate x ω) -
        (indexedEndpoint hd Q ν ζ P T β a μ t) ω)
        (ENNReal.ofReal p) (reducedLaw Q)) (𝓝 0) (𝓝 0) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hp2 : 2 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  let lift (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) := hf.toLp f
  have hlift (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      complexLpToL2 (reducedLaw Q) hp2 (lift f hf) = f := by
    apply Lp.ext
    exact hf.coeFn_toLp
  have hforward (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      ∃ F : ℝ≥0 → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        Continuous F ∧ ∀ t, (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          centeredComplexLp Q (P t f) := by
    let F := fun t => hP.lpRestriction hp t (lift f hf)
    have hF : Continuous F := (hP.lpRestriction_c0 hp).2.2 _
    have he (t) : (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P t f := by
      have hh := hP.lpRestriction_apply hp t (lift f hf)
      rw [hlift] at hh
      exact Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℂ 2 (reducedLaw Q) => (g : FieldPair d → ℂ)) hh)
    exact ⟨fun t => EndpointFiniteP.center (F t),
      EndpointFiniteP.center.continuous.comp hF,
      fun t => EndpointFiniteP.center_ae_l2 Q (F t) (P t f) (he t)⟩
  obtain ⟨K, _hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hβp (j) : MemLp (β j) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (β j)).aestronglyMeasurable K (hb j)
  have hap (j k) : MemLp (a j k) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (a j k)).aestronglyMeasurable K (ha' j k)
  have hμp : MemLp μ (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable K hm
  have hw : ∃ F : ℝ≥0 → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      Continuous F ∧ ∀ t, (F t : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P T β a μ t := by
    cases ν with
    | inl j =>
      have hf : MemLp (β j + ζ • a ⟨0, by omega⟩ j)
          (ENNReal.ofReal p) (reducedLaw Q) :=
        (memLp_congr_ae (Lp.coeFn_add _ _)).2 ((hβp j).add
          ((memLp_congr_ae (Lp.coeFn_smul _ _)).2 ((hap _ j).const_smul ζ)))
      exact hforward _ hf
    | inr b =>
      cases b with
      | false =>
        obtain ⟨F, hF, he⟩ := hforward μ hμp
        refine ⟨fun t => ζ • F t, hF.const_smul ζ, fun t => ?_⟩
        exact (Lp.coeFn_smul ζ (F t)).trans
          (((he t).const_smul ζ).trans (Lp.coeFn_smul ζ _).symm)
      | true =>
        refine ⟨fun t => hT.lpRestriction hp hP t (lift (β ⟨0, by omega⟩) (hβp _)),
          (hT.lpRestriction_c0 hp hP).2.2 _, fun t => ?_⟩
        have hh := hT.lpRestriction_apply hp hP t (lift (β ⟨0, by omega⟩) (hβp _))
        rw [hlift] at hh
        exact Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℂ 2 (reducedLaw Q) => (g : FieldPair d → ℂ)) hh)
  obtain ⟨F, hF, he⟩ := hw
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let f := F t
  let τ : Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun x =>
    Lp.compMeasurePreserving (translate x)
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x) f
  let g : Vec d → C(FieldPair d, FieldPair d) := fun x =>
    ⟨translate x, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate
  have hc : Continuous τ := continuous_const.compMeasurePreservingLp hg
    (fun x => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
    ENNReal.ofReal_ne_top
  have hzero : τ 0 = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) 0)] with ω hω
    simpa only [Function.comp_apply, translate_zero] using hω
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' τ f).mp
    (by simpa only [hzero] using hc.tendsto 0)
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro x
  apply eLpNorm_congr_ae
  have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
  exact ((Lp.coeFn_compMeasurePreserving f hm).trans
    (hm.quasiMeasurePreserving.ae (he t))).sub (he t)

end EinsteinFull.Blueprint
