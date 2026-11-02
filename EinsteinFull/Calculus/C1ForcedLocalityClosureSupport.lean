import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment
import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! The explicit retained environment for paper/main.tex:669–670,715.
This constructs a jointly local coefficient pair. No evolution or comparison
estimate for that pair is asserted here. -/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinFull.ForcedLocality
open EinsteinRelation

/-- Apply the same deterministic cutoff to both coordinates of the environment. -/
def retainedPair {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d) : FieldPair d :=
  (⟨fun x => χ x • ω.1 x + (1 - χ x) • (1 : Mat d),
    (χ.continuous.smul ω.1.continuous).add
      ((continuous_const.sub χ.continuous).smul continuous_const)⟩,
   ⟨fun x => χ x * ω.2 x + (1 - χ x),
    (χ.continuous.mul ω.2.continuous).add (continuous_const.sub χ.continuous)⟩)

/-- The retained pair equals the actual pair wherever the cutoff is one. -/
theorem retainedPair_eq_at {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    {x : Vec d} (hx : χ x = 1) :
    (retainedPair χ ω).1 x = ω.1 x ∧ (retainedPair χ ω).2 x = ω.2 x := by
  simp only [retainedPair, ContinuousMap.coe_mk, hx, sub_self, zero_smul,
    one_smul, add_zero, one_mul, and_self]

/-- Outside the cutoff support the pair is exactly `(Id,1)`. -/
theorem retainedPair_fixed_at {d : ℕ} (χ : C(Vec d, ℝ)) (ω : FieldPair d)
    {x : Vec d} (hx : χ x = 0) :
    (retainedPair χ ω).1 x = (1 : Mat d) ∧ (retainedPair χ ω).2 x = 1 := by
  simp only [retainedPair, ContinuousMap.coe_mk, hx, sub_zero, zero_smul,
    one_smul, zero_add, zero_mul, and_self]

/-- The whole retained field is measurable from the joint restrictions to `U`.
At boundary points outside `U` the cutoff must vanish. -/
theorem measurable_retainedPair {d : ℕ} (χ : C(Vec d, ℝ)) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) :
    Measurable[localSigma U] (retainedPair χ) := by
  let : MeasurableSpace (FieldPair d) := localSigma U
  apply measurable_fieldPair_of_evaluations
  intro x
  by_cases hx : x ∈ U
  · have he : Measurable (fun ω : FieldPair d => (ω.1 x, ω.2 x)) := by
      apply Measurable.of_comap_le
      exact le_iSup_of_le (⟨x, hx⟩ : U) le_rfl
    change Measurable (fun ω : FieldPair d =>
      (χ x • ω.1 x + (1 - χ x) • (1 : Mat d), χ x * ω.2 x + (1 - χ x)))
    exact ((he.fst.const_smul (χ x)).add_const _).prodMk
      ((he.snd.const_mul (χ x)).add_const _)
  · have he : (fun ω : FieldPair d =>
        ((retainedPair χ ω).1 x, (retainedPair χ ω).2 x)) =
        fun _ => ((1 : Mat d), (1 : ℝ)) := by
      funext ω
      exact Prod.ext (retainedPair_fixed_at χ ω (hχ x hx)).1
        (retainedPair_fixed_at χ ω (hχ x hx)).2
    rw [he]
    exact measurable_const

/-- Any Borel observable of the retained pair has the same joint locality. -/
theorem measurable_comp_retainedPair {d : ℕ} {E : Type*} [MeasurableSpace E]
    (χ : C(Vec d, ℝ)) (U : Set (Vec d)) (hχ : ∀ x, x ∉ U → χ x = 0)
    (F : FieldPair d → E) (hF : Measurable F) :
    Measurable[localSigma U] (fun ω => F (retainedPair χ ω)) :=
  hF.comp (measurable_retainedPair χ U hχ)

/-- Spatial coefficient derivatives agree on the retained open region.
This is an equality of actual derivatives, without a smoothness premise. -/
theorem retainedPair_coordinateDerivative {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) {U : Set (Vec d)} (hU : IsOpen U)
    (hχ : ∀ y ∈ U, χ y = 1) {x : Vec d} (hx : x ∈ U) (i j k : Fin d) :
    coordinateDerivative k (fun y => (retainedPair χ ω).1 y i j) x =
      coordinateDerivative k (fun y => ω.1 y i j) x := by
  have he : (fun y => (retainedPair χ ω).1 y i j) =ᶠ[𝓝 x]
      (fun y => ω.1 y i j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact congrArg (fun A : Mat d => A i j) (retainedPair_eq_at χ ω (hχ y hy)).1
  exact congrArg (fun L => L (unitVector k)) (he.fderiv_eq (𝕜 := ℝ))

/-- In particular the actual divergence drift is unchanged on the retained
open region, so forward and transpose sources use the same coefficients. -/
theorem retainedPair_drift {d : ℕ} (χ : C(Vec d, ℝ))
    (ω : FieldPair d) {U : Set (Vec d)} (hU : IsOpen U)
    (hχ : ∀ y ∈ U, χ y = 1) {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    (1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => (retainedPair χ ω).1 y j i) x =
      (1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => ω.1 y j i) x := by
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    retainedPair_coordinateDerivative χ ω hU hχ hx j i j

/-- The cutoff dependency's existential pair is this explicit pair, with all
its ellipticity, clock and derivative bounds on the same environment event.
Constants and cutoff are chosen before the law. -/
theorem exists_retainedPair
    (hcut : Blueprint.node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (D : StructuralData d) :
    ∃ Λ : ℝ, ∃ M : ℕ → ℝ, 1 ≤ Λ ∧
      (∀ k : ℕ, 1 ≤ k → 0 < M k) ∧
    ∃ χ : Vec d → ℝ → C(Vec d, ℝ),
      (∀ z ρ, 1 ≤ ρ →
        Measurable[localSigma {x : Vec d | euclideanNorm (x - z) < 2 * ρ}]
          (retainedPair (χ z ρ))) ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
          ∀ z ρ, 1 ≤ ρ →
            (∀ x, euclideanNorm (x - z) ≤ ρ →
              (retainedPair (χ z ρ) ω).1 x = ω.1 x ∧
              (retainedPair (χ z ρ) ω).2 x = ω.2 x) ∧
            (∀ x, 2 * ρ ≤ euclideanNorm (x - z) →
              (retainedPair (χ z ρ) ω).1 x = (1 : Mat d) ∧
              (retainedPair (χ z ρ) ω).2 x = 1) ∧
            IsElliptic Λ (retainedPair (χ z ρ) ω).1 ∧
            (∀ x, Λ⁻¹ ≤ (retainedPair (χ z ρ) ω).2 x ∧
              (retainedPair (χ z ρ) ω).2 x ≤ Λ) ∧
            IsSmoothWithBounds M (retainedPair (χ z ρ) ω) := by
  classical
  obtain ⟨Λ, M, K, hΛ, hMK, χ, hχ, hpair⟩ := hcut d D
  let ψ : Vec d → ℝ → C(Vec d, ℝ) := fun z ρ =>
    if hρ : 1 ≤ ρ then ⟨χ z ρ, (hχ z ρ hρ).1.continuous⟩ else 0
  have hψ (z : Vec d) (ρ : ℝ) (hρ : 1 ≤ ρ) (x : Vec d) :
      ψ z ρ x = χ z ρ x := by simp only [ψ, dite_eq_left hρ, ContinuousMap.coe_mk]
  refine ⟨Λ, M, hΛ, fun k hk => (hMK k hk).1, ψ, ?_, ?_⟩
  · intro z ρ hρ
    apply measurable_retainedPair
    intro x hx
    rw [hψ z ρ hρ]
    exact (hχ z ρ hρ).2.2.2.1 x (le_of_not_gt hx)
  · intro Q hQ
    filter_upwards [hpair Q hQ] with ω hω
    intro z ρ hρ
    obtain ⟨ωloc, ha, hμ, hin, hout, hell, hclock, hsmooth⟩ := hω z ρ hρ
    have he : retainedPair (ψ z ρ) ω = ωloc := by
      apply Prod.ext
      · ext x j k
        simpa only [retainedPair, ContinuousMap.coe_mk, hψ z ρ hρ] using
          congrArg (fun A : Mat d => A j k) (ha x).symm
      · ext x
        simpa only [retainedPair, ContinuousMap.coe_mk, hψ z ρ hρ] using (hμ x).symm
    rw [he]
    exact ⟨hin, hout, hell, hclock, hsmooth⟩

end EinsteinFull.ForcedLocality
