import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Calculus.C1FluxSchwartzSiteBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory EinsteinRelation

namespace EinsteinFull.Blueprint

/-- Conditional expectation preserves the eight-block site estimate. -/
theorem c1_actual_eight_blocks_condExp_bound
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (q : ENNReal) (hq : 1 ≤ q) (m : MeasurableSpace (FieldPair d))
    (c₀ c₁ : ℂ) (U : Bool → Bool → FieldPair d → ℂ)
    (B : Bool → FieldPair d → ℂ) (T : Bool → ℝ) (w : ℝ)
    (hU : ∀ b a, MemLp (U b a) q (reducedLaw Q))
    (hB : ∀ b, MemLp (B b) q (reducedLaw Q))
    (hUE : ∀ b a, MemLp (U b a - (reducedLaw Q)[U b a | m]) q (reducedLaw Q))
    (hBE : ∀ b, MemLp (B b - (reducedLaw Q)[B b | m]) q (reducedLaw Q))
    (hUb : ∀ b a, (eLpNorm
      (U b a - (reducedLaw Q)[U b a | m]) q (reducedLaw Q)).toReal ≤ T b * w)
    (hBb : ∀ b, (eLpNorm
      (B b - (reducedLaw Q)[B b | m]) q (reducedLaw Q)).toReal ≤ T b * w) :
    let f := c₀ • ((U true false - B true) + Complex.I • (U true true - B true)) -
      c₁ • ((U false false - B false) + Complex.I • (U false true - B false))
    MemLp (f - (reducedLaw Q)[f | m]) q (reducedLaw Q) ∧
      (eLpNorm (f - (reducedLaw Q)[f | m]) q (reducedLaw Q)).toReal ≤
        (4 * ‖c₀‖ * T true + 4 * ‖c₁‖ * T false) * w := by
  letI := reducedLaw_probability Q
  let μ := reducedLaw Q
  let F := fun b => (U b false - B b) + Complex.I • (U b true - B b)
  have hF (b : Bool) : MemLp (F b) q μ :=
    ((hU b false).sub (hB b)).add (((hU b true).sub (hB b)).const_smul Complex.I)
  have hbranch (b : Bool) : μ[F b | m] =ᵐ[μ]
      (μ[U b false | m] - μ[B b | m]) +
        Complex.I • (μ[U b true | m] - μ[B b | m]) := by
    have h₀ := condExp_sub ((hU b false).integrable hq) ((hB b).integrable hq) m
    have h₁ := condExp_sub ((hU b true).integrable hq) ((hB b).integrable hq) m
    have hi := condExp_smul (μ := μ) Complex.I (U b true - B b) m
    have ha := condExp_add (((hU b false).sub (hB b)).integrable hq)
      ((((hU b true).sub (hB b)).const_smul Complex.I).integrable hq) m
    filter_upwards [h₀, h₁, hi, ha] with ω h₀ h₁ hi ha
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    change μ[(U b false - B b) + Complex.I • (U b true - B b) | m] ω = _
    rw [ha, hi, h₀, h₁]
  have hs₀ := condExp_smul (μ := μ) c₀ (F true) m
  have hs₁ := condExp_smul (μ := μ) c₁ (F false) m
  have hs := condExp_sub ((hF true).const_smul c₀ |>.integrable hq)
    ((hF false).const_smul c₁ |>.integrable hq) m
  have heq : (c₀ • F true - c₁ • F false - μ[c₀ • F true - c₁ • F false | m]) =ᵐ[μ]
      c₀ • (((U true false - μ[U true false | m]) - (B true - μ[B true | m])) +
        Complex.I • ((U true true - μ[U true true | m]) - (B true - μ[B true | m]))) -
      c₁ • (((U false false - μ[U false false | m]) - (B false - μ[B false | m])) +
        Complex.I • ((U false true - μ[U false true | m]) - (B false - μ[B false | m]))) := by
    filter_upwards [hbranch true, hbranch false, hs₀, hs₁, hs] with ω ht hf hs₀ hs₁ hs
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [hs, hs₀, hs₁, ht, hf]
    dsimp [F]
    ring
  have h := c1_actual_eight_blocks_site_bound Q q hq c₀ c₁
    (fun b a => U b a - μ[U b a | m]) (fun b => B b - μ[B b | m]) T w
    hUE hBE hUb hBb
  dsimp only at h ⊢
  refine ⟨MemLp.ae_eq heq.symm h.1, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact h.2

end EinsteinFull.Blueprint
