import EinsteinFull.Calculus.C12SharpActualAverageRate
import EinsteinFull.Calculus.S2ForwardFamily
import EinsteinFull.Blueprint.Roots.node_t_u3A_expansion
import EinsteinFull.Blueprint.G4.node_e_u3A_division
import EinsteinFull.Blueprint.Foundation.Proofs.D1PathwiseV2
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Blueprint.Foundation.Proofs.S2ForcedClockV2
import EinsteinFull.Calculus.CLForcedLLNV2

/-!
# The velocity expansion (`t:expansion`)

The root follows from `e:division` alone. For a smooth law, the reduced drift, coefficient and
clock observations, the commutator joint observation and its covariance exist; `e:division`
expands `η⁻¹ ℓ`, the reduced velocity divided by the reduced clock rate. A signed physical family
has a reduced family related to it by the inverse clock (`exists_reducedFamily_of_signedPhysical`).
The forced clock identity (the closed proof of `eq.time-change-identities#forced-clock` from its
proved dependencies) gives `v = η⁻¹ ℓ` for the physical velocity `v`, which is unique.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Clock.InverseMeaningV3

/-- The forced clock identity, closed from its proved dependencies. -/
theorem tExpansion_forcedClock :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2 :=
  node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock_of_deps
    (node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln_of_deps
      node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps
      node_eq_u2E_reduced_u2D_bounds_of_deps)
    node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps

/-- The reduced drift, coefficient and clock observations and the commutator joint observation of
a smooth law (as in `C12SharpActualAverageRate`). -/
theorem tExpansion_observations {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) :
    ∃ (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β ∧ IsReducedCoefficientObservation Q a ∧
        IsReducedClockObservation Q μ ∧ IsJointObservation Q Z := by
  classical
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨_, _, hβ⟩ := response_reduced_drift_exists_uniform_bound d D
  obtain ⟨β, hβ, _⟩ := hβ Q hQ
  have ha (j k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
      2 (reducedLaw Q) := (memLp_reduced_coefficient_complex Q j k).mono_exponent le_top
  have hm : MemLp (fun ω : FieldPair d => (ω.2 0 : ℂ)) 2 (reducedLaw Q) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.comp
        ((continuous_eval_const (0 : Vec d)).comp continuous_snd)).aestronglyMeasurable
      (sourceReducedBound D.ellipticity)
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
      reducedLaw, Carriers.reducedReferenceLaw] using
      Clock.ae_abs_clockAtOrigin_le Q
  have hXi (j i : Fin d) : MemLp
      (fun ω => (commutatorObservation Q j i ω : ℂ)) 2 (reducedLaw Q) := by
    have hg := (memLp_const (Correctors.correctorUnitVector i)
      (p := (2 : ENNReal)) (μ := reducedLaw Q)).add (Lp.memLp (correctorGradient Q i))
    apply hg.of_le_mul (c := (d : ℝ) * (2 * sourceReducedBound D.ellipticity))
      (Complex.measurable_ofReal.comp
        (EinsteinFull.Calculus.C2TestReplacement.commutatorObservation_measurable Q j i)).aestronglyMeasurable
    simpa only [Function.comp_apply, Pi.add_apply, Complex.norm_real, Real.norm_eq_abs] using
      EinsteinFull.Calculus.C2TestReplacement.ae_abs_commutatorObservation_le Q j i
  have hc : MemLp (fun ω => (centeredClockField Q 0 ω : ℂ)) 2 (reducedLaw Q) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.comp ((continuous_centeredClockField Q).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      (2 * sourceReducedBound D.ellipticity)
    simpa only [Function.comp_apply, id_eq, Complex.norm_real, Real.norm_eq_abs] using
      ae_abs_centeredClockField_le Q 0
  refine ⟨β, (fun j k => (ha j k).toLp _), hm.toLp _,
    (fun z => match z with
      | .inl (j, i) => (hXi j i).toLp _
      | .inr () => hc.toLp _), hβ, (fun j k => (ha j k).coeFn_toLp),
    hm.coeFn_toLp, (fun j i => (hXi j i).coeFn_toLp), ?_⟩
  exact hc.coeFn_toLp

/-- The joint covariance of a joint observation (as in `C12SharpActualAverageRate`). -/
theorem tExpansion_joint_covariance {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z) :
    ∃ covariance, IsJointCovariance Q Z covariance := by
  obtain ⟨ε, C, hε, _hC, h⟩ :=
    EinsteinFull.Proofs.covariance_scaling d hd D (2 * d + 11) (by omega)
  obtain ⟨covariance, _hpos, _hbound, hrate⟩ := h Q hQ
  refine ⟨covariance, w2_jointCovariance_of_rate Q Z covariance
    (2 * d + 11) ε C hε ?_⟩
  intro R hR F G
  rw [jointTestCovariance_eq_integral]
  exact hrate Z hZ R hR F G

/-- `t:expansion` from `e:division`. -/
theorem node_t_u3A_expansion_of_deps (hdivision : node_e_u3A_divisionStmt) :
    node_t_u3A_expansionStmt := by
  intro d hd D
  obtain ⟨C, lamStar, hC, hstar, hstarE, hdiv⟩ := hdivision d hd D
  obtain ⟨Λ, _hΛ, hclock⟩ := tExpansion_forcedClock D.ellipticity D.one_le_ellipticity
  refine ⟨C, lamStar, hC.le, hstar, hstarE, fun Q hQ => ?_⟩
  have : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨β, a, μ, Z, hβ, ha, hμ, hZ⟩ := tExpansion_observations D Q hQ
  obtain ⟨covariance, hcovariance⟩ := tExpansion_joint_covariance hd D Q hQ Z hZ
  obtain ⟨_hγ, recip, b, c, _h0, _hr0, _hrn, _hb, _hc, hnorm, _hb0, hcov0, hbound⟩ :=
    hdiv Q hQ β a μ Z covariance hβ ha hμ hZ hcovariance
      (forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d))
      (fun ζ => isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ ζ)
  refine ⟨b, c, ?_, fun P hP => ?_⟩
  · have hr : 0 ≤ ∑ n, |recip n| := Finset.sum_nonneg fun n _ => abs_nonneg _
    linarith
  intro cov hcov
  refine ⟨hcov0 P hP cov hcov, fun velocity hvelocity lam hlam hsmall => ?_⟩
  have hsmooth : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := hQ.mono fun _ h => h.1
  obtain ⟨Y, hYMP, hrel⟩ := exists_reducedFamily_of_signedPhysical
    (⟨0, by omega⟩ : Fin d) Q hsmooth P hP
  have hlam0 : lam ≠ 0 := abs_pos.mp hlam
  obtain ⟨η, vX, vY, _hη1, _hη2, hη, hvX, hvY, _, _, _, hvXY⟩ :=
    hclock d hd D.dependenceRange D.derivativeBound Q D.one_le_dependenceRange
      D.derivativeBound_pos hQ lam hlam0 (P lam) (Y lam) (hP lam) (hYMP lam) (hrel lam)
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P lam) ω) :=
    (hP lam).mono fun _ h => h.1
  have hv : velocity lam = vX := HasQuenchedVelocity.unique hprob (hvelocity lam hlam0) hvX
  have h := (hbound lam hlam hsmall (hsmall.trans hstarE) (Y lam) (hYMP lam) vY η hvY hη).2.2.2.2.1
  rw [hv, hvXY]
  exact h

end EinsteinFull.Blueprint
