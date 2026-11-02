import EinsteinFull.Calculus.ComplexForceApproximationSupport
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Contractive evolutions of the shifted forced Yosida generators

Operator exponentials of the proved bounded Yosida approximations form
strongly continuous contraction semigroups. Their derivative is the actual
bounded Yosida generator, not a replacement weak generator. This constructs
the approximating evolutions only; the stationary generator limit is separate.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Operator exponential evolution of an actual bounded shifted forced Yosida generator. -/
def forcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (t : ℝ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  NormedSpace.exp (t • forcedComplexYosida Q i ζ n)

/-- Each bounded Yosida evolution starts at the identity. -/
theorem forcedComplexYosidaEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) :
    forcedComplexYosidaEvolution Q i ζ n 0 = ContinuousLinearMap.id ℂ _ := by
  change NormedSpace.exp ((0 : ℝ) • forcedComplexYosida Q i ζ n) = _
  have hz : (0 : ℝ) • forcedComplexYosida Q i ζ n = 0 := by
    exact zero_smul ℝ (forcedComplexYosida Q i ζ n)
  rw [hz, NormedSpace.exp_zero]
  rfl

/-- Each bounded Yosida evolution satisfies the semigroup law. -/
theorem forcedComplexYosidaEvolution_add {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (s t : ℝ) :
    forcedComplexYosidaEvolution Q i ζ n (s+t) =
      (forcedComplexYosidaEvolution Q i ζ n s).comp (forcedComplexYosidaEvolution Q i ζ n t) := by
  letI : NormedAlgebra ℝ (Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :=
    .restrictScalars ℝ ℂ _
  letI : NormedAlgebra ℚ (Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :=
    .restrictScalars ℚ ℂ _
  unfold forcedComplexYosidaEvolution
  change NormedSpace.exp ((s + t) • forcedComplexYosida Q i ζ n) =
    (NormedSpace.exp (s • forcedComplexYosida Q i ζ n)).comp
      (NormedSpace.exp (t • forcedComplexYosida Q i ζ n))
  have hcomm : Commute (s • forcedComplexYosida Q i ζ n)
      (t • forcedComplexYosida Q i ζ n) := by
    apply ContinuousLinearMap.ext
    intro f
    change s • forcedComplexYosida Q i ζ n (t • forcedComplexYosida Q i ζ n f) =
      t • forcedComplexYosida Q i ζ n (s • forcedComplexYosida Q i ζ n f)
    have hlin (r : ℝ) (v : Lp ℂ 2 (reducedLaw Q)) :
        forcedComplexYosida Q i ζ n (r • v) = r • forcedComplexYosida Q i ζ n v :=
      (forcedComplexYosida Q i ζ n |>.restrictScalars ℝ).map_smul r v
    rw [hlin, hlin, smul_smul, smul_smul, mul_comm s t]
  rw [show (s+t) • forcedComplexYosida Q i ζ n =
    s • forcedComplexYosida Q i ζ n + t • forcedComplexYosida Q i ζ n from by simpa using! (add_smul s t (forcedComplexYosida Q i ζ n)),
    NormedSpace.exp_add_of_commute hcomm]
  rfl

/-- Differentiating a bounded Yosida evolution gives that same actual bounded generator. -/
theorem hasDerivAt_forcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    HasDerivAt (fun s => forcedComplexYosidaEvolution Q i ζ n s f)
      (forcedComplexYosida Q i ζ n (forcedComplexYosidaEvolution Q i ζ n t f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) f).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (forcedComplexYosida Q i ζ n) t)
  exact h

/-- Each bounded Yosida evolution is strongly continuous in time. -/
theorem continuous_forcedComplexYosidaEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => forcedComplexYosidaEvolution Q i ζ n t f) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_forcedComplexYosidaEvolution Q i ζ n f t).continuousAt

private theorem realL2_inner_eq_re {d : ℕ} (Q : Measure (FieldPair d)) (f g : Lp ℂ 2 Q) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Dissipativity makes every bounded Yosida evolution contractive at nonnegative time. -/
theorem norm_forcedComplexYosidaEvolution_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) (ht : 0 ≤ t) : ‖forcedComplexYosidaEvolution Q i ζ n t f‖ ≤ ‖f‖ := by
  have hd (s : ℝ) := (hasDerivAt_forcedComplexYosidaEvolution Q i ζ n f s).norm_sq
  have hm := antitone_of_hasDerivAt_nonpos hd (fun s => ?_)
  · have hb := hm ht
    change ‖forcedComplexYosidaEvolution Q i ζ n t f‖ ^ 2 ≤
      ‖forcedComplexYosidaEvolution Q i ζ n 0 f‖ ^ 2 at hb
    rw [forcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply] at hb
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb
  · rw [realL2_inner_eq_re]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (forcedComplexYosida_re_inner_nonpos Q i ζ n _)

/-- The bounded Yosida evolution has operator norm at most one at nonnegative time. -/
theorem norm_forcedComplexYosidaEvolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖forcedComplexYosidaEvolution Q i ζ n t‖ ≤ 1 := by
  apply (forcedComplexYosidaEvolution Q i ζ n t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using norm_forcedComplexYosidaEvolution_apply_le Q i ζ n f t ht

private theorem hasDerivAt_evolution_right {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    HasDerivAt (fun s => forcedComplexYosidaEvolution Q i ζ n s f)
      (forcedComplexYosidaEvolution Q i ζ n t (forcedComplexYosida Q i ζ n f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) f).restrictScalars ℝ
  exact E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (forcedComplexYosida Q i ζ n) t)

/-- Integrating the evolved bounded generator gives the exact Yosida orbit increment. -/
theorem integral_forcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
      forcedComplexYosidaEvolution Q i ζ n s (forcedComplexYosida Q i ζ n f)) =
        forcedComplexYosidaEvolution Q i ζ n t f - f := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := t)
    (fun s _ => hasDerivAt_evolution_right Q i ζ n f s)
    ((continuous_forcedComplexYosidaEvolution_apply Q i ζ n
      (forcedComplexYosida Q i ζ n f)).intervalIntegrable 0 t)
  simpa only [forcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply] using h

/-- The Yosida orbit increment is controlled by its initial bounded generator value. -/
theorem norm_forcedComplexYosidaEvolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 ≤ t) :
    ‖forcedComplexYosidaEvolution Q i ζ n t f - f‖ ≤ t * ‖forcedComplexYosida Q i ζ n f‖ := by
  rw [← integral_forcedComplexYosidaEvolution Q i ζ n f t]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
    (fun s hs => norm_forcedComplexYosidaEvolution_apply_le Q i ζ n
      (forcedComplexYosida Q i ζ n f) s
      (by rw [Set.uIoc_of_le ht] at hs; exact hs.1.le))
  simpa only [sub_zero, abs_of_nonneg ht, mul_comm] using h

/-- Full generator-domain data have an orbit increment bound uniform in the Yosida index. -/
theorem IsComplexGeneratorPair.forced_yosida_evolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖forcedComplexYosidaEvolution Q i ζ n t f - f‖ ≤ t * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖ := by
  have he := hfg.forcedComplexYosida_eq n
  exact (norm_forcedComplexYosidaEvolution_sub_le Q i ζ n f t ht).trans
    (mul_le_mul_of_nonneg_left
      (he ▸ norm_forcedComplexResolventApproximation_le Q i ζ n
        (g - (complexForceShift d Λ₀ ζ : ℂ) • f)) ht)

end EinsteinFull
