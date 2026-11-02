import EinsteinFull.Calculus.C16KmRequestedActionReduction

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The bounded endpoint action of the actual supplied reduced martingale law
agrees almost everywhere with the physical complex environment evolution. -/
def S3KMSuppliedBoundedAction : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
  letI := reducedLaw_probability Q
  ∀ (lam : ℝ) (_h0 : 0 ≤ lam) (_h1 : lam ≤ 1) (Y : QuenchedPathLaws d),
    (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (Y (0,ω))) →
    ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (FieldPair d) ℂ),
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0,ω)) =ᵐ[Q.measure]
        (fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd)
          (lam : ℂ) t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))

/-- Uniform positive-force coupling existence and nonreturn, with parameters
chosen before the joint law and force. -/
def S3KMAdmissibleCouplingNonreturn : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
  ∃ L : ℝ, 0 < L ∧ r₀ < 2 * L ∧
  ∀ l : ℝ, L ≤ l →
  ∃ δa lamc : ℝ, 0 < δa ∧ δa < 1 ∧ 0 < lamc ∧ lamc ≤ 1 ∧
  ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1),
    lam ≤ lamc → ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∃ _hK : IsRegenerationCoupling hd Q lam l δa h0.le h1 P K,
      Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0

/-- Conditional exact k/m decomposition, using the same supplied law in the
bounded-action input and a separately supplied nonreturn coupling. -/
theorem s3_km_decomp_of_requested_bounded_action
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (haction : S3KMSuppliedBoundedAction)
    (hcoupling : S3KMAdmissibleCouplingNonreturn) :
    node_rt_u3A_km_u2D_decompStmt :=
  c16_km_decomp_of_requested_bounded_action haction hcoupling hfactor hphase hmany hrem

end EinsteinFull.Blueprint
