import EinsteinRelation.Probability.ConditionalLocalVersions

open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinRelation.Probability
attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- Source `paper/main.tex:383–387`: conditional resampling constructs a jointly measurable local version, retaining both origin and spatial-a.e. clauses. -/
theorem exists_parameter_local_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d))
    (f : Vec d × FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (Vec d × FieldPair d))
    (hGo : ∀ᵐ ω ∂Q, (0, ω) ∈ G)
    (hGp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q, p ∈ G)
    (hlocal : ∀ x ω, (x, ω) ∈ G → ∀ ω', (x, ω') ∈ G →
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → f (x, ω) = f (x, ω')) :
    ∃ A : Vec d × FieldPair d → ℝ,
      @Measurable (Vec d × FieldPair d) ℝ ((borel (Vec d)).prod (localSigma U))
        inferInstance A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = f (0, ω)) ∧
      A =ᵐ[(volume : Measure (Vec d)).prod Q] f := by
  let m : MeasurableSpace (Vec d × FieldPair d) :=
    (inferInstance : MeasurableSpace (Vec d)).prod (localSigma U)
  let κ : @Kernel (Vec d × FieldPair d) (FieldPair d) m inferInstance :=
    (condExpKernel Q (localSigma U)).comap Prod.snd measurable_snd
  let A : Vec d × FieldPair d → ℝ := fun p => ∫ ω', f (p.1, ω') ∂condExpKernel Q (localSigma U) p.2
  have hA : @Measurable (Vec d × FieldPair d) ℝ m inferInstance A := by
    have h : @Measurable ((Vec d × FieldPair d) × FieldPair d) ℝ
        (m.prod inferInstance) inferInstance (fun p => f (p.1.1, p.2)) :=
      hf.comp (((@measurable_fst (Vec d) (FieldPair d) inferInstance (localSigma U)).comp
        (@measurable_fst (Vec d × FieldPair d) (FieldPair d) m inferInstance)).prodMk
          (@measurable_snd (Vec d × FieldPair d) (FieldPair d) m inferInstance))
    exact (h.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hgen : ∀ x : Vec d, (∀ᵐ ω ∂Q, (x, ω) ∈ G) →
      ∀ᵐ ω ∂Q, A (x, ω) = f (x, ω) := by
    intro x hx
    filter_upwards [hx, ae_condExpKernel_of_ae Q (localSigma U)
      (localSigma_le_borel U) hx, ae_condExpKernel_fields_eq_on Q U] with ω hω hgood heq
    have hconst : ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω, f (x, ω') = f (x, ω) := by
      filter_upwards [hgood, heq] with ω' hω' heq'
      exact (hlocal x ω hω ω' hω' heq').symm
    dsimp only [A]
    rw [integral_congr_ae hconst]
    simp
  refine ⟨A, ?_, hgen 0 hGo, ?_⟩
  · simpa only [← BorelSpace.measurable_eq (α := Vec d)] using hA
  · have hle : m ≤ ((inferInstance : MeasurableSpace (Vec d)).prod
        (inferInstance : MeasurableSpace (FieldPair d))) := by
      change MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Vec d)) ⊔
        MeasurableSpace.comap Prod.snd (localSigma U) ≤ _
      exact sup_le
        (@measurable_fst (Vec d) (FieldPair d) inferInstance inferInstance).comap_le
        ((MeasurableSpace.comap_mono (localSigma_le_borel U)).trans
          (@measurable_snd (Vec d) (FieldPair d) inferInstance inferInstance).comap_le)
    have hAf : @Measurable (Vec d × FieldPair d) ℝ
        ((inferInstance : MeasurableSpace (Vec d)).prod
          (inferInstance : MeasurableSpace (FieldPair d))) inferInstance A :=
      hA.mono hle le_rfl
    apply (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure (Vec d))) (ν := Q)
      (measurableSet_eq_fun hAf hf)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hGp] with x hx
    exact hgen x hx


end EinsteinRelation.Probability
