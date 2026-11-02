import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_clock
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Blueprint.G3.Proofs.C1ClockAnalyticity
import EinsteinFull.Calculus.C1EndpointFiniteP
/-! Partial support for analytic clock representatives. The finite-p flux is
constructed from an actual analytic finite-p gradient, and the full shared
representative contract is proved in L2. Finite-p gradient regularity remains
open; the exact supervisor target below is preserved as a comment. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Multiplication by the actual coefficient entry on the finite-p quotient. -/
private def clockCoefficientMul {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : Fin d) :
    Lp ℂ p (reducedLaw Q) →L[ℂ] Lp ℂ p (reducedLaw Q) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ p p
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ)))

private theorem clockCoefficientMul_coe {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : Fin d)
    (f : Lp ℂ p (reducedLaw Q)) :
    (clockCoefficientMul Q p j k f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (ω.1 0 j k : ℂ) * f ω := by
  have hc := (memLp_reduced_coefficient_complex Q j k).coeFn_toLp
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := p)
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ))) f
  filter_upwards [hc, hm] with ω ha hb
  simpa only [clockCoefficientMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ha] using hb

/-- Carrier transfer only: an analytic finite-p gradient determines the actual
anisotropic finite-p flux. This does not establish finite-p gradient regularity. -/
theorem clock_flux_representatives_of_gradient {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (G : ℂ → Fin d → Lp ℂ 2 (reducedLaw Q))
    (Gp : ℂ → Fin d → Lp ℂ p (reducedLaw Q))
    (hG : ∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] G ζ j)
    (s : Set ℂ) (hGp : ∀ j, DifferentiableOn ℂ (fun ζ => Gp ζ j) s) :
    ∃ Jp : ℂ → Fin d → Lp ℂ p (reducedLaw Q),
      (∀ ζ j, (Jp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        ClockAnalyticity.flux Q (G ζ) j) ∧
      ∀ j, DifferentiableOn ℂ (fun ζ => Jp ζ j) s := by
  let Jp : ℂ → Fin d → Lp ℂ p (reducedLaw Q) := fun ζ j =>
    ∑ k, (clockCoefficientMul Q p j k (Gp ζ k) -
      (homogenizedCoefficient Q j k : ℂ) • Gp ζ k)
  refine ⟨Jp, ?_, ?_⟩
  · intro ζ j
    have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin d))
      (fun k => clockCoefficientMul Q p j k (Gp ζ k) -
        (homogenizedCoefficient Q j k : ℂ) • Gp ζ k)
    have hsl := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin d))
      (fun k => complexCoefficientMul Q j k (G ζ k) -
        (homogenizedCoefficient Q j k : ℂ) • G ζ k)
    have he (k : Fin d) :
        ((clockCoefficientMul Q p j k (Gp ζ k) -
          (homogenizedCoefficient Q j k : ℂ) • Gp ζ k : Lp ℂ p (reducedLaw Q)) :
            FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        ((complexCoefficientMul Q j k (G ζ k) -
          (homogenizedCoefficient Q j k : ℂ) • G ζ k : Lp ℂ 2 (reducedLaw Q)) :
            FieldPair d → ℂ) := by
      filter_upwards [Lp.coeFn_sub (clockCoefficientMul Q p j k (Gp ζ k))
          ((homogenizedCoefficient Q j k : ℂ) • Gp ζ k),
        Lp.coeFn_sub (complexCoefficientMul Q j k (G ζ k))
          ((homogenizedCoefficient Q j k : ℂ) • G ζ k),
        clockCoefficientMul_coe Q p j k (Gp ζ k),
        complexCoefficientMul_coe Q j k (G ζ k),
        Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) (Gp ζ k),
        Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) (G ζ k), hG ζ k]
        with ω hp hl hmp hml hsp hsl hgl
      simp only [hp, hl, hmp, hml, hsp, hsl, Pi.sub_apply, Pi.smul_apply, hgl]
    filter_upwards [hs, hsl, ae_all_iff.mpr he] with ω hp hl he
    change (∑ k, (clockCoefficientMul Q p j k (Gp ζ k) -
      (homogenizedCoefficient Q j k : ℂ) • Gp ζ k)) ω = _
    rw [hp]
    change _ = (∑ k, (complexCoefficientMul Q j k (G ζ k) -
      (homogenizedCoefficient Q j k : ℂ) • G ζ k)) ω
    rw [hl]
    exact Finset.sum_congr rfl (fun k _ => he k)
  · intro j
    exact DifferentiableOn.fun_sum (fun k _ =>
      (((clockCoefficientMul Q p j k).differentiable.comp_differentiableOn
        (hGp k)).sub ((hGp k).const_smul (homogenizedCoefficient Q j k : ℂ))))

/-- The representative clauses of the assigned contract hold at exponent two,
with the same weak-flux witnesses at every positive time. -/
theorem clock_l2_shared_analytic_representatives {d : ℕ} (hd : 2 ≤ d) {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (μ : Lp ℂ 2 (reducedLaw Q))
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) :
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ (r : ℝ≥0), 0 < (r : ℝ) →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r) ∧
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (clockEndpoint Q ζ (P ζ) μ r)
          (fun j => ζ • G ζ r j) (fun j => ζ • J ζ r j)) ∧
      ∀ (r : ℝ≥0), 0 < (r : ℝ) →
      ∃ Wp : ℂ → Lp ℂ 2 (reducedLaw Q),
      ∃ Gp Jp : ℂ → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ ζ, (Wp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (centeredComplexLp Q (P ζ r μ) : FieldPair d → ℂ)) ∧
        (∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] G ζ r j ∧
          (Jp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] J ζ r j) ∧
        Differentiable ℂ Wp ∧
        (∀ j, Differentiable ℂ (fun ζ => Gp ζ j) ∧
          Differentiable ℂ (fun ζ => Jp ζ j)) := by
  obtain ⟨G, J, hflux, han⟩ := clockL2Witnesses hd Q a ha μ P hP
  refine ⟨G, J, fun ζ r hr => hflux ζ r (by exact_mod_cast hr), ?_⟩
  intro r hr
  refine ⟨fun ζ => centeredComplexLp Q (P ζ r μ), fun ζ => G ζ r,
    fun ζ => J ζ r, fun _ => Filter.EventuallyEq.rfl,
    fun _ _ => ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩, ?_, ?_⟩
  · intro ζ
    have h := ((centeredComplexLpCLM Q).analyticAt _).comp
      (analyticAt_complexEnvironmentSemigroup_apply hP r (z₀ := ζ)
        (analyticAt_const (v := μ)))
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using h.differentiableAt
  · intro j
    exact ⟨fun ζ => (han r (by exact_mod_cast hr) j ζ).1.differentiableAt,
      fun ζ => (han r (by exact_mod_cast hr) j ζ).2.differentiableAt⟩

/- SUPERVISOR EXACT TARGET (not a declaration or proof); replace with proved command.
theorem analytic_clock_gradient_flux_representatives_of_deps
  (h0 : EinsteinFull.Blueprint.node_stationary_u2D_analytic_u2D_semigroupStmt)
  (h1 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_fluxStmt)
  (h2 : EinsteinFull.Blueprint.node_p_u3A_scalarStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p B : ℝ) (hp : 2 ≤ p), 2 ≤ B →
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩

    ∃ C t₀ : ℝ, ∃ N : ℕ, 0 < C ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ (r : ℝ≥0), 0 < (r : ℝ) →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r) ∧
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (clockEndpoint Q ζ (P ζ) μ r)
          (fun j => ζ • G ζ r j) (fun j => ζ • J ζ r j)) ∧
      ∀ (r : ℝ≥0), t₀ ≤ (r : ℝ) →
      ∃ Wp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      ∃ Gp Jp : ℂ → Fin d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ ζ, (Wp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (centeredComplexLp Q (P ζ r μ) : FieldPair d → ℂ)) ∧
        (∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] G ζ r j ∧
          (Jp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] J ζ r j) ∧
        DifferentiableOn ℂ Wp {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1} ∧
        (∀ j, DifferentiableOn ℂ (fun ζ => Gp ζ j)
          {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1} ∧
          DifferentiableOn ℂ (fun ζ => Jp ζ j)
          {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1})
-/
end EinsteinFull.Blueprint
