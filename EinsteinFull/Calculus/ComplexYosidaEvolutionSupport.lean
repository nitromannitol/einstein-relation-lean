import EinsteinFull.Calculus.ComplexResolventApproximationSupport
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Contractive evolutions of the actual bounded Yosida generators

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

/-- Operator exponential evolution of an actual bounded unforced Yosida generator. -/
def unforcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (t : ℝ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  NormedSpace.exp (t • unforcedComplexYosida Q i n)

/-- Each bounded Yosida evolution starts at the identity. -/
theorem unforcedComplexYosidaEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) :
    unforcedComplexYosidaEvolution Q i n 0 = ContinuousLinearMap.id ℂ _ := by
  change NormedSpace.exp ((0 : ℝ) • unforcedComplexYosida Q i n) = _
  have hz : (0 : ℝ) • unforcedComplexYosida Q i n = 0 := by
    exact zero_smul ℝ (unforcedComplexYosida Q i n)
  rw [hz, NormedSpace.exp_zero]
  rfl

/-- Each bounded Yosida evolution satisfies the semigroup law. -/
theorem unforcedComplexYosidaEvolution_add {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (s t : ℝ) :
    unforcedComplexYosidaEvolution Q i n (s+t) =
      (unforcedComplexYosidaEvolution Q i n s).comp (unforcedComplexYosidaEvolution Q i n t) := by
  letI : NormedAlgebra ℝ (Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :=
    .restrictScalars ℝ ℂ _
  letI : NormedAlgebra ℚ (Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :=
    .restrictScalars ℚ ℂ _
  unfold unforcedComplexYosidaEvolution
  change NormedSpace.exp ((s + t) • unforcedComplexYosida Q i n) =
    (NormedSpace.exp (s • unforcedComplexYosida Q i n)).comp
      (NormedSpace.exp (t • unforcedComplexYosida Q i n))
  have hcomm : Commute (s • unforcedComplexYosida Q i n)
      (t • unforcedComplexYosida Q i n) := by
    apply ContinuousLinearMap.ext
    intro f
    change s • unforcedComplexYosida Q i n (t • unforcedComplexYosida Q i n f) =
      t • unforcedComplexYosida Q i n (s • unforcedComplexYosida Q i n f)
    have hlin (r : ℝ) (v : Lp ℂ 2 (reducedLaw Q)) :
        unforcedComplexYosida Q i n (r • v) = r • unforcedComplexYosida Q i n v :=
      (unforcedComplexYosida Q i n |>.restrictScalars ℝ).map_smul r v
    rw [hlin, hlin, smul_smul, smul_smul, mul_comm s t]
  rw [show (s+t) • unforcedComplexYosida Q i n =
    s • unforcedComplexYosida Q i n + t • unforcedComplexYosida Q i n from by simpa using! (add_smul s t (unforcedComplexYosida Q i n)),
    NormedSpace.exp_add_of_commute hcomm]
  rfl

/-- Differentiating a bounded Yosida evolution gives that same actual bounded generator. -/
theorem hasDerivAt_unforcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    HasDerivAt (fun s => unforcedComplexYosidaEvolution Q i n s f)
      (unforcedComplexYosida Q i n (unforcedComplexYosidaEvolution Q i n t f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) f).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (unforcedComplexYosida Q i n) t)
  exact h

/-- Each bounded Yosida evolution is strongly continuous in time. -/
theorem continuous_unforcedComplexYosidaEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => unforcedComplexYosidaEvolution Q i n t f) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_unforcedComplexYosidaEvolution Q i n f t).continuousAt

private theorem realL2_inner_eq_re {d : ℕ} (Q : Measure (FieldPair d)) (f g : Lp ℂ 2 Q) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- Dissipativity makes every bounded Yosida evolution contractive at nonnegative time. -/
theorem norm_unforcedComplexYosidaEvolution_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) (ht : 0 ≤ t) : ‖unforcedComplexYosidaEvolution Q i n t f‖ ≤ ‖f‖ := by
  have hd (s : ℝ) := (hasDerivAt_unforcedComplexYosidaEvolution Q i n f s).norm_sq
  have hm := antitone_of_hasDerivAt_nonpos hd (fun s => ?_)
  · have hb := hm ht
    change ‖unforcedComplexYosidaEvolution Q i n t f‖ ^ 2 ≤
      ‖unforcedComplexYosidaEvolution Q i n 0 f‖ ^ 2 at hb
    rw [unforcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply] at hb
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb
  · rw [realL2_inner_eq_re]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (unforcedComplexYosida_re_inner_nonpos Q i n _)

/-- The bounded Yosida evolution has operator norm at most one at nonnegative time. -/
theorem norm_unforcedComplexYosidaEvolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖unforcedComplexYosidaEvolution Q i n t‖ ≤ 1 := by
  apply (unforcedComplexYosidaEvolution Q i n t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using norm_unforcedComplexYosidaEvolution_apply_le Q i n f t ht

private theorem hasDerivAt_evolution_right {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    HasDerivAt (fun s => unforcedComplexYosidaEvolution Q i n s f)
      (unforcedComplexYosidaEvolution Q i n t (unforcedComplexYosida Q i n f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) f).restrictScalars ℝ
  exact E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (unforcedComplexYosida Q i n) t)

/-- Integrating the evolved bounded generator gives the exact Yosida orbit increment. -/
theorem integral_unforcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    (∫ s in (0 : ℝ)..t,
      unforcedComplexYosidaEvolution Q i n s (unforcedComplexYosida Q i n f)) =
        unforcedComplexYosidaEvolution Q i n t f - f := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := t)
    (fun s _ => hasDerivAt_evolution_right Q i n f s)
    ((continuous_unforcedComplexYosidaEvolution_apply Q i n
      (unforcedComplexYosida Q i n f)).intervalIntegrable 0 t)
  simpa only [unforcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply] using h

/-- The Yosida orbit increment is controlled by its initial bounded generator value. -/
theorem norm_unforcedComplexYosidaEvolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 ≤ t) :
    ‖unforcedComplexYosidaEvolution Q i n t f - f‖ ≤ t * ‖unforcedComplexYosida Q i n f‖ := by
  rw [← integral_unforcedComplexYosidaEvolution Q i n f t]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
    (fun s hs => norm_unforcedComplexYosidaEvolution_apply_le Q i n
      (unforcedComplexYosida Q i n f) s
      (by rw [Set.uIoc_of_le ht] at hs; exact hs.1.le))
  simpa only [sub_zero, abs_of_nonneg ht, mul_comm] using h

/-- Full generator-domain data have an orbit increment bound uniform in the Yosida index. -/
theorem IsComplexGeneratorPair.unforced_yosida_evolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖unforcedComplexYosidaEvolution Q i n t f - f‖ ≤ t * ‖g‖ := by
  have he : unforcedComplexYosida Q i n f =
      unforcedComplexResolventApproximation Q i n g := by
    change (((n : ℝ) + 1 : ℝ) : ℂ) •
      ((((n : ℝ) + 1 : ℝ) : ℂ) •
        unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity) f - f) = _
    rw [hfg.unforced_resolvent_error]
    rfl
  exact (norm_unforcedComplexYosidaEvolution_sub_le Q i n f t ht).trans
    (mul_le_mul_of_nonneg_left (he ▸ norm_unforcedComplexResolventApproximation_le Q i n g) ht)

end EinsteinFull
