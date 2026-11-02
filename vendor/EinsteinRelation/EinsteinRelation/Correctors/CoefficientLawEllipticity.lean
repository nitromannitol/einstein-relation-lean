import EinsteinRelation.Environment.CoefficientRestriction
import EinsteinRelation.Environment.Bounds
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Matrix

/-! # Ellipticity of the reduced coefficient law

Source: paper/main.tex:196–207 (§time change; `eq.reduced-bounds` gives
`Λ⁻¹ I ≤ a ≤ Λ I` for the reduced coefficient `a = exp(-2V) a₀`, with `Λ ≥ 1` depending on
the bound `Λ₀`) and paper/main.tex:686–701 (§corrector estimates, which work with the reduced
coefficient law).

The target statement is the body of the frozen signature
`EinsteinRelation.Proposal.coefficientLawEllipticity` (general02 signature v2). That declaration
is not yet in the repository, so the theorem
`EinsteinRelation.Correctors.ae_coefficientLaw_isElliptic` carries that body verbatim as its type.
The parameter is `Λ = exp(2L) * L`, where `L` is the bound `Λ₀` of the physical environment.

Proof outline:
* `reducedCoefficient_energy_bounds` (Environment.Bounds) bounds the quadratic form of the reduced
  coefficient below by `exp(-2L) * L⁻¹`, which is exactly `(exp(2L) * L)⁻¹`.
* The coefficient fields that are elliptic with parameter `Λ` form a closed subset of the
  compact-open carrier, hence a measurable set: an intersection of closed evaluation conditions
  indexed by points and directions.
* `MeasureTheory.ae_map_iff` transports the almost-sure statement along `reducedMatrixField`,
  using the measurability of that set and the almost-sure regularity `Q.regular`.

No isotropy, no additional ellipticity premise, and no law-dependent constant is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The upper parameter has the exact inverse `(exp(2L) * L)⁻¹ = exp(-2L) * L⁻¹`. -/
private theorem inv_exp_two_mul_mul (L : ℝ) :
    (Real.exp (2 * L) * L)⁻¹ = Real.exp (-2 * L) * L⁻¹ := by
  have h : Real.exp (-2 * L) = (Real.exp (2 * L))⁻¹ := by
    rw [← Real.exp_neg, neg_mul]
  rw [mul_inv, h]

/-- Evaluation at a fixed point is continuous on the compact-open coefficient carrier. -/
private theorem continuous_coefficient_eval {d : ℕ} (x : Vec d) :
    Continuous fun F : CoefficientField d => F x :=
  continuous_eval_const x

/-- Transposition at a fixed point is continuous on coefficient fields. -/
private theorem continuous_transpose_eval {d : ℕ} (x : Vec d) :
    Continuous fun F : CoefficientField d => (F x).transpose :=
  (continuous_coefficient_eval x).matrix_transpose

/-- For a fixed direction `ξ`, the quadratic form `M ↦ ξ · (M ξ)` is continuous in `M`. -/
private theorem continuous_dot_mulVec_matrix {d : ℕ} (ξ : Vec d) :
    Continuous fun M : Mat d => dot ξ (M.mulVec ξ) := by
  have hmul : Continuous fun M : Mat d => M.mulVec ξ :=
    continuous_id.matrix_mulVec continuous_const
  show Continuous fun M : Mat d => ∑ i, ξ i * (M.mulVec ξ) i
  exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp hmul)

/-- Ellipticity with a fixed parameter `Λ` is a closed condition on coefficient fields: it is the
intersection over points `x` and directions `ξ` of closed symmetry and quadratic-form bounds. -/
private theorem isClosed_isElliptic_field {d : ℕ} (Λ : ℝ) :
    IsClosed {F : CoefficientField d | IsElliptic Λ (fun x => F x)} := by
  have hset : {F : CoefficientField d | IsElliptic Λ (fun x => F x)} =
      ⋂ x : Vec d, ({F : CoefficientField d | (F x).transpose = F x} ∩
        ⋂ ξ : Vec d, ({F : CoefficientField d | Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((F x).mulVec ξ)} ∩
          {F : CoefficientField d | dot ξ ((F x).mulVec ξ) ≤ Λ * euclideanSq ξ})) := by
    ext F
    simp only [IsElliptic, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isClosed_iInter fun x => IsClosed.inter
    (isClosed_eq (continuous_transpose_eval x) (continuous_coefficient_eval x))
    (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
  · exact isClosed_le continuous_const
      ((continuous_dot_mulVec_matrix ξ).comp (continuous_coefficient_eval x))
  · exact isClosed_le ((continuous_dot_mulVec_matrix ξ).comp (continuous_coefficient_eval x))
      continuous_const

/-- The reduced coefficient of a regular environment is elliptic with parameter `exp(2L) * L` at
every point, with the exact inverse `(exp(2L) * L)⁻¹ = exp(-2L) * L⁻¹` on the lower side. -/
private theorem isElliptic_reducedMatrixField {d : ℕ} {L : ℝ} (hL : 1 ≤ L) {ω : FieldPair d}
    (hω : IsRegular L ω) :
    IsElliptic (Real.exp (2 * L) * L) (fun x => reducedMatrixField ω x) := by
  intro x
  refine ⟨reducedCoefficient_transpose ω x (hω.1 x).1, fun ξ => ?_⟩
  rw [inv_exp_two_mul_mul L]
  exact reducedCoefficient_energy_bounds ω x ξ L hL hω

/-- Source: paper/main.tex:196–207 and 686–701. For every environment law, almost every
coefficient field of the reduced coefficient law is elliptic with parameter
`Λ = exp(2L) * L`, where `L` is the ellipticity bound of the physical environment. -/
theorem ae_coefficientLaw_isElliptic :
    ∀ {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀),
      ∀ᵐ (F : CoefficientField d) ∂coefficientLaw Q.measure,
        IsElliptic (Real.exp (2*L)*L) (fun x => F x) := by
  intro d L r₀ Q
  unfold coefficientLaw
  refine (ae_map_iff (measurable_reducedMatrixField (d := d)).aemeasurable
    (isClosed_isElliptic_field (d := d) (Real.exp (2 * L) * L)).measurableSet).2 ?_
  filter_upwards [Q.regular] with ω hω
  exact isElliptic_reducedMatrixField Q.ellipticity_parameter hω

end EinsteinRelation.Correctors
