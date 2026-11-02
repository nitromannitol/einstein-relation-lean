import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Actual horizontal derivatives on a bounded smooth orbit core

Source `paper/main.tex:240–248`, translations and horizontal integration by parts.
Every derivative below is computed from the literal orbit x ↦ F(translate x ω)
using the shared spatial Fréchet derivative. Measurability is proved by pointwise
limits of measurable difference quotients; no continuity of F in ω is assumed.
Stationarity and dominated differentiation prove zero mean derivative.

The bounded smooth core is a concrete class of test representatives. Identifying
its closure with the full L² generator domain/H¹, and extending IBP to all H¹,
remain separate internal obligations. No source theorem is narrowed to this core.
-/

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace EinsteinRelation

/-- An actual observable evaluated along the environment translation orbit. -/
def orbit {d : ℕ} (F : FieldPair d → ℝ) (ω : FieldPair d) (x : Vec d) : ℝ :=
  F (translate x ω)

/-- Literal iterated coordinate derivatives of a spatial function. -/
def coordinateIterate {d : ℕ} : List (Fin d) → (Vec d → ℝ) → Vec d → ℝ
  | [], f => f
  | i :: rest, f => coordinateDerivative i (coordinateIterate rest f)

/-- A bounded smooth orbit core. Full L² generator-domain equivalence is separate. -/
def IsHorizontalTest {d : ℕ} (F : FieldPair d → ℝ) : Prop :=
  Measurable F ∧ (∀ ω, ContDiff ℝ (⊤ : ℕ∞) (orbit F ω)) ∧
  ∀ coordinates : List (Fin d), ∃ M : ℝ,
    ∀ ω x, |coordinateIterate coordinates (orbit F ω) x| ≤ M

/-- The horizontal coordinate derivative is the actual spatial derivative at the origin. -/
def horizontalDerivative {d : ℕ} (i : Fin d) (F : FieldPair d → ℝ) (ω : FieldPair d) : ℝ :=
  coordinateDerivative i (orbit F ω) 0

@[simp] theorem orbit_zero {d : ℕ} (F : FieldPair d → ℝ) (ω : FieldPair d) :
    orbit F ω 0 = F ω := by simp [orbit]

theorem orbit_translate {d : ℕ} (F : FieldPair d → ℝ) (ω : FieldPair d) (x y : Vec d) :
    orbit F (translate x ω) y = orbit F ω (x + y) := by
  simp only [orbit, translate_add, add_comm y x]

theorem horizontalDerivative_translate {d : ℕ} (i : Fin d) (F : FieldPair d → ℝ)
    (ω : FieldPair d) (x : Vec d) :
    horizontalDerivative i F (translate x ω) = coordinateDerivative i (orbit F ω) x := by
  have hfun : orbit F (translate x ω) = fun y => orbit F ω (x + y) :=
    funext (orbit_translate F ω x)
  simp only [horizontalDerivative, coordinateDerivative, hfun, fderiv_comp_add_left, add_zero]

theorem hasDerivAt_orbit_line {d : ℕ} (i : Fin d) (F : FieldPair d → ℝ)
    (ω : FieldPair d) (t : ℝ)
    (hF : DifferentiableAt ℝ (orbit F ω) (t • unitVector i)) :
    HasDerivAt (fun u : ℝ => orbit F ω (u • unitVector i))
      (coordinateDerivative i (orbit F ω) (t • unitVector i)) t := by
  simpa only [Function.comp_def, id_eq, one_smul, coordinateDerivative] using
    hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (unitVector i))

/-- Measurability of pointwise parameter derivatives requires no continuity in the sample. -/
theorem measurable_parameter_derivative {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℝ) (g : Ω → ℝ) (hf : ∀ t, Measurable (f t))
    (hg : ∀ ω, HasDerivAt (fun t => f t ω) (g ω) 0) : Measurable g := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : Tendsto s atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      change 0 < 1 / ((n : ℝ) + 1)
      positivity
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => (s n)⁻¹ * (f (s n) ω - f 0 ω))
    (fun n => ((hf (s n)).sub (hf 0)).const_mul _)
  apply tendsto_pi_nhds.mpr
  intro ω
  simpa only [Function.comp_def, zero_add, smul_eq_mul] using
    (hg ω).tendsto_slope_zero_right.comp hs

/-- Actual horizontal derivatives are measurable from measurable observations and orbit differentiability. -/
theorem measurable_horizontalDerivative {d : ℕ} (i : Fin d) (F : FieldPair d → ℝ)
    (hF : Measurable F) (hder : ∀ ω, DifferentiableAt ℝ (orbit F ω) 0) :
    Measurable (horizontalDerivative i F) := by
  refine measurable_parameter_derivative (fun t ω => orbit F ω (t • unitVector i))
    (horizontalDerivative i F) (fun t => hF.comp (Probability.measurable_translate _)) ?_
  intro ω
  have h := hasDerivAt_orbit_line i F ω 0 (by simpa using hder ω)
  rw [zero_smul] at h
  exact h

theorem IsHorizontalTest.measurable_derivative {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) : Measurable (horizontalDerivative i F) :=
  measurable_horizontalDerivative i F hF.1
    (fun ω => (hF.2.1 ω).differentiable (by simp) |>.differentiableAt)

theorem IsHorizontalTest.bound_orbit {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ ω x, |orbit F ω x| ≤ M := by
  obtain ⟨M, hM⟩ := hF.2.2 []
  exact ⟨|M|, abs_nonneg M, fun ω x => (hM ω x).trans (le_abs_self M)⟩

theorem IsHorizontalTest.bound_derivative {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (i : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ω x, |coordinateDerivative i (orbit F ω) x| ≤ M := by
  obtain ⟨M, hM⟩ := hF.2.2 [i]
  exact ⟨|M|, abs_nonneg M, fun ω x => (hM ω x).trans (le_abs_self M)⟩

/-- The actual bounded core observable has every finite-measure Lp moment. -/
theorem IsHorizontalTest.memLp {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (p : ENNReal) : MemLp F p Q := by
  obtain ⟨B, _hB0, hB⟩ := hF.bound_orbit
  refine MemLp.of_bound hF.1.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => ?_)
  simpa only [Real.norm_eq_abs, orbit_zero] using hB ω 0

/-- Each actual core derivative belongs in particular to the L² spaces used by
entropy and the corrector variational problem. -/
theorem IsHorizontalTest.memLp_derivative {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (p : ENNReal) (i : Fin d) : MemLp (horizontalDerivative i F) p Q := by
  obtain ⟨B, _hB0, hB⟩ := hF.bound_derivative i
  exact MemLp.of_bound (hF.measurable_derivative i).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hB ω 0)

/-- Stationarity and bounded actual orbit derivatives give zero mean horizontal derivative. -/
theorem integral_horizontalDerivative_eq_zero_of_bounded {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (i : Fin d) (F : FieldPair d → ℝ) (hF : Measurable F)
    (hder : ∀ ω x, DifferentiableAt ℝ (orbit F ω) x)
    (hb : ∃ M : ℝ, ∀ ω x, |orbit F ω x| ≤ M)
    (hbd : ∃ M : ℝ, ∀ ω x, |coordinateDerivative i (orbit F ω) x| ≤ M) :
    (∫ ω, horizontalDerivative i F ω ∂Q) = 0 := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨D, hD⟩ := hbd
  have hmeas : ∀ t : ℝ, Measurable (fun ω => orbit F ω (t • unitVector i)) :=
    fun t => hF.comp (Probability.measurable_translate _)
  have hmeasD : AEStronglyMeasurable
      (fun ω => coordinateDerivative i (orbit F ω) ((0 : ℝ) • unitVector i)) Q := by
    simp only [zero_smul]
    exact (measurable_horizontalDerivative i F hF (fun ω => hder ω 0)).aestronglyMeasurable
  have hF0 : Integrable (fun ω => orbit F ω ((0 : ℝ) • unitVector i)) Q :=
    Integrable.of_bound (hmeas 0).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hB ω _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Q) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t ω => orbit F ω (t • unitVector i))
    (F' := fun t ω => coordinateDerivative i (orbit F ω) (t • unitVector i))
    (bound := fun _ => D) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable)
    hF0 hmeasD
    (Filter.Eventually.of_forall fun ω t _ => by simpa only [Real.norm_eq_abs] using hD ω _)
    (integrable_const D)
    (Filter.Eventually.of_forall fun ω t _ => hasDerivAt_orbit_line i F ω t (hder ω _))
  have hconst : (fun t : ℝ => ∫ ω, orbit F ω (t • unitVector i) ∂Q) =
      fun _ => ∫ ω, F ω ∂Q := by
    funext t
    exact Probability.integral_translate Q hQ _ F hF
  have hz := h.2
  rw [hconst] at hz
  have heq := hz.unique (hasDerivAt_const (0 : ℝ) (∫ ω, F ω ∂Q))
  have heq' : ∫ ω, coordinateDerivative i (orbit F ω) ((0 : ℝ) • unitVector i) ∂Q = 0 := heq
  simp only [zero_smul] at heq'
  exact heq'

/-- Zero-mean derivative on the actual bounded smooth core, not an assumed IBP field. -/
theorem IsHorizontalTest.integral_derivative_eq_zero {d : ℕ} {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) :
    (∫ ω, horizontalDerivative i F ω ∂Q) = 0 := by
  obtain ⟨B, _, hB⟩ := hF.bound_orbit
  obtain ⟨D, _, hD⟩ := hF.bound_derivative i
  exact integral_horizontalDerivative_eq_zero_of_bounded Q hQ i F hF.1
    (fun ω x => (hF.2.1 ω).differentiable (by simp) |>.differentiableAt)
    ⟨B, hB⟩ ⟨D, hD⟩

end EinsteinRelation
