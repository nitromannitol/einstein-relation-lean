import EinsteinFull.Calculus.S3AnnuliSupport
import EinsteinFull.Frozen.ComplexLocalObservation
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Complex-linear conditional expectation on the actual finite-p carrier.
This is support for the pending V2 endpoint reduction, not that reduction. -/

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace EinsteinFull.EndpointProjection

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Conditional expectation as a finite-p class. -/
def project (f : Lp ℂ p μ) : Lp ℂ p μ :=
  ((Lp.memLp f).condExp (Fact.out : 1 ≤ p) (m := m)).toLp _

omit [IsFiniteMeasure μ] in
/-- The selected finite-p class has the literal conditional expectation as representative. -/
theorem project_ae (f : Lp ℂ p μ) :
    (project (m := m) f : Ω → ℂ) =ᵐ[μ] μ[(f : Ω → ℂ) | m] :=
  MemLp.coeFn_toLp _

omit [IsFiniteMeasure μ] in
/-- The projection is contractive in the finite-p norm. -/
theorem norm_project_le (f : Lp ℂ p μ) : ‖project (m := m) f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (project_ae f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_condExp_le_eLpNorm _ (Fact.out : 1 ≤ p))

/-- Complex linearity and boundedness hold on the actual Lp quotient. -/
def projectionCLM : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := project (m := m)
      map_add' := fun f g => by
        apply Lp.ext
        exact (project_ae (f + g)).trans
          ((condExp_congr_ae (Lp.coeFn_add f g)).trans
            ((condExp_add ((Lp.memLp f).integrable (Fact.out : 1 ≤ p))
              ((Lp.memLp g).integrable (Fact.out : 1 ≤ p)) m).trans
              (((project_ae f).add (project_ae g)).symm.trans
                (Lp.coeFn_add _ _).symm)))
      map_smul' := fun z f => by
        apply Lp.ext
        exact (project_ae (z • f)).trans
          ((condExp_congr_ae (Lp.coeFn_smul z f)).trans
            ((condExp_smul z (f : Ω → ℂ) m).trans
              (((project_ae f).const_smul z).symm.trans (Lp.coeFn_smul z _).symm))) }
    1 (fun f => by
      change ‖project (m := m) f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_project_le f)

/-- A fixed projection preserves differentiability of a force family. -/
theorem differentiableOn_project {s : Set ℂ} {E : ℂ → Lp ℂ p μ}
    (hE : DifferentiableOn ℂ E s) :
    DifferentiableOn ℂ (fun z => project (m := m) (E z)) s :=
  (projectionCLM (μ := μ) (m := m) (p := p)).differentiable.comp_differentiableOn hE

/-- Projection preserves the literal expectation, so centered families remain centered. -/
theorem integral_project (hm : m ≤ m0) (f : Lp ℂ p μ) :
    (∫ ω, project (m := m) f ω ∂μ) = ∫ ω, f ω ∂μ := by
  rw [integral_congr_ae (project_ae f), integral_condExp hm]

/-- The finite-p projection has the same L2 representative as the L2 projection.
The L2 datum is constructed from the given finite-p class, without a new premise. -/
theorem project_ae_condExpL2 (hm : m ≤ m0) (hp : 2 ≤ p) (f : Lp ℂ p μ) :
    (project (m := m) f : Ω → ℂ) =ᵐ[μ]
      (condExpL2 ℂ ℂ hm ((Lp.memLp f).mono_exponent hp).toLp : Ω → ℂ) := by
  exact (project_ae f).trans
    (((Lp.memLp f).mono_exponent hp).condExpL2_ae_eq_condExp hm).symm

private instance reducedProbability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

/-- The L2 representative of the finite-p projection is genuinely local. -/
theorem exists_local_l2 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EinsteinRelation.EnvironmentLaw d Λ₀ r₀) (ρ : ℝ)
    (hp : 2 ≤ p) (f : Lp ℂ p (reducedLaw Q)) :
    ∃ f₂ : Lp ℂ 2 (reducedLaw Q),
      (project (m := EinsteinRelation.localSigma
        {x : EinsteinRelation.Vec d | EinsteinRelation.euclideanNorm x < ρ}) f :
          EinsteinRelation.FieldPair d → ℂ) =ᵐ[reducedLaw Q] f₂ ∧
        IsComplexLocalObservation Q ρ f₂ := by
  let hm := EinsteinRelation.Probability.localSigma_le_borel
    {x : EinsteinRelation.Vec d | EinsteinRelation.euclideanNorm x < ρ}
  let f₂ : Lp ℂ 2 (reducedLaw Q) :=
    condExpL2 ℂ ℂ hm ((Lp.memLp f).mono_exponent hp).toLp
  refine ⟨f₂, project_ae_condExpL2 hm hp f, ?_⟩
  have ha := aestronglyMeasurable_condExpL2 (𝕜 := ℂ) hm ((Lp.memLp f).mono_exponent hp).toLp
  exact ⟨ha.mk _, ha.stronglyMeasurable_mk.measurable, ha.ae_eq_mk.symm⟩

end EinsteinFull.EndpointProjection
