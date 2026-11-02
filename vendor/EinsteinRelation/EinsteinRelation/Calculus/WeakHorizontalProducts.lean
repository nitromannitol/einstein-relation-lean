import EinsteinRelation.Calculus.WeakChainRule
import EinsteinRelation.Calculus.HorizontalIntegration

/-! # Products with smooth horizontal observables

Source: `paper/main.tex:1034–1059`, Steps 3 and 4 of Proposition 6.1.
The local correctors in the two-scale expansion have weak horizontal gradients.
Multiplication by a bounded smooth horizontal observable obeys the usual product
rule, with the same full generator tests as `HasWeakHorizontalGradient`.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-- Coordinate iterates preserve smoothness. -/
theorem contDiff_coordinateIterate {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateIterate cs f) := by
  induction cs with
  | nil => exact hf
  | cons i cs ih =>
    exact ((contDiff_infty_iff_fderiv.mp ih).2).clm_apply contDiff_const

/-- Coordinate iterates distribute over sums of smooth spatial functions. -/
theorem coordinateIterate_add {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (cs : List (Fin d)) :
    coordinateIterate cs (fun x => f x + g x) =
      fun x => coordinateIterate cs f x + coordinateIterate cs g x := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
    funext x
    simp only [coordinateIterate, ih, coordinateDerivative]
    rw [fderiv_fun_add ((contDiff_coordinateIterate hf cs).differentiable (by simp) x)
      ((contDiff_coordinateIterate hg cs).differentiable (by simp) x)]
    rfl

/-- The iterated spatial derivative and the corresponding iterated observable agree. -/
theorem orbit_iteratedHorizontalDerivative (cs : List (Fin d)) (f : FieldPair d → ℝ)
    (ω : FieldPair d) :
    orbit (iteratedHorizontalDerivative cs f) ω = coordinateIterate cs (orbit f ω) := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
    simp only [iteratedHorizontalDerivative, orbit_horizontalDerivative, ih, coordinateIterate]

/-- A sum of bounded smooth horizontal observables is a bounded smooth observable. -/
theorem IsHorizontalTest.add {f g : FieldPair d → ℝ}
    (hf : IsHorizontalTest f) (hg : IsHorizontalTest g) :
    IsHorizontalTest (fun ω => f ω + g ω) := by
  refine ⟨hf.1.add hg.1, fun ω => (hf.2.1 ω).add (hg.2.1 ω), fun cs => ?_⟩
  obtain ⟨A, hA⟩ := hf.2.2 cs
  obtain ⟨B, hB⟩ := hg.2.2 cs
  refine ⟨A + B, fun ω x => ?_⟩
  change |coordinateIterate cs (fun y => orbit f ω y + orbit g ω y) x| ≤ _
  rw [coordinateIterate_add (hf.2.1 ω) (hg.2.1 ω)]
  exact (abs_add_le _ _).trans (add_le_add (hA ω x) (hB ω x))

/-- Products are closed in the actual bounded smooth orbit core. -/
theorem IsHorizontalTest.mul {f g : FieldPair d → ℝ}
    (hf : IsHorizontalTest f) (hg : IsHorizontalTest g) :
    IsHorizontalTest (fun ω => f ω * g ω) := by
  refine ⟨hf.1.mul hg.1, fun ω => (hf.2.1 ω).mul (hg.2.1 ω), ?_⟩
  intro cs
  induction cs using List.reverseRecOn generalizing f g with
  | nil =>
    obtain ⟨A, hA0, hA⟩ := hf.bound_orbit
    obtain ⟨B, _, hB⟩ := hg.bound_orbit
    exact ⟨A * B, fun ω x => by
      change |orbit f ω x * orbit g ω x| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hA ω x) (hB ω x) (abs_nonneg _) hA0⟩
  | append_singleton cs i ih =>
    obtain ⟨A, hA⟩ := ih hf (hg.horizontalDerivative i)
    obtain ⟨B, hB⟩ := ih hg (hf.horizontalDerivative i)
    refine ⟨A + B, fun ω x => ?_⟩
    rw [coordinateIterate_append_single]
    have heq : coordinateDerivative i (orbit (fun η => f η * g η) ω) =
        fun y => orbit f ω y * orbit (EinsteinRelation.horizontalDerivative i g) ω y +
          orbit g ω y * orbit (EinsteinRelation.horizontalDerivative i f) ω y := by
      funext y
      change coordinateDerivative i (fun z => orbit f ω z * orbit g ω z) y = _
      rw [coordinateDerivative_mul i _ _ y
        ((hf.2.1 ω).differentiable (by simp) y)
        ((hg.2.1 ω).differentiable (by simp) y)]
      rw [orbit_horizontalDerivative, orbit_horizontalDerivative]
    rw [heq, coordinateIterate_add
      ((hf.2.1 ω).mul ((hg.horizontalDerivative i).2.1 ω))
      ((hg.2.1 ω).mul ((hf.horizontalDerivative i).2.1 ω))]
    exact (abs_add_le _ _).trans (add_le_add (hA ω x) (hB ω x))

/-- Multiplication by a bounded smooth horizontal observable preserves integrability. -/
theorem IsHorizontalTest.integrable_mul {Q : Measure (FieldPair d)} {g f : FieldPair d → ℝ}
    (hg : IsHorizontalTest g) (hf : Integrable f Q) :
    Integrable (fun ω => f ω * g ω) Q := by
  obtain ⟨B, _, hB⟩ := hg.bound_orbit
  exact hf.mul_bdd hg.1.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs, orbit_zero] using hB ω 0)

/-- Multiplication of a weak horizontal gradient by a bounded smooth observable
(`paper/main.tex:1034–1044`). The conclusion uses every horizontally smooth
`L²` generator test, rather than only tests in the concrete orbit core. -/
theorem HasWeakHorizontalGradient.mul_horizontalTest {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} {g : FieldPair d → ℝ}
    (hf : HasWeakHorizontalGradient Q hQ f Df) (hfm : Measurable f)
    (hDfm : Measurable Df) (hg : IsHorizontalTest g) :
    HasWeakHorizontalGradient Q hQ (fun ω => f ω * g ω)
      (fun ω i => g ω * Df ω i + f ω * horizontalDerivative i g ω) := by
  have hgi (i : Fin d) : Integrable (fun ω =>
      g ω * Df ω i + f ω * horizontalDerivative i g ω) Q := by
    have h₁ := hg.integrable_mul (hf.2.1 i)
    have h₂ := (hg.horizontalDerivative i).integrable_mul hf.1
    simpa only [mul_comm (g _)] using! h₁.add h₂
  have hcore (i : Fin d) (K : FieldPair d → ℝ) (hK : IsHorizontalTest K) :
      (∫ ω, (f ω * g ω) * horizontalDerivative i K ω ∂Q) =
        -(∫ ω, (g ω * Df ω i + f ω * horizontalDerivative i g ω) * K ω ∂Q) := by
    have hp := Calculus.weakPairing_core hf i (hg.mul hK)
    have hsplit : (fun ω => f ω * horizontalDerivative i (fun η => g η * K η) ω) =
        fun ω => (f ω * g ω) * horizontalDerivative i K ω +
          (f ω * horizontalDerivative i g ω) * K ω := by
      funext ω
      rw [horizontalDerivative_mul i g K ω
        ((hg.2.1 ω).differentiable (by simp) 0)
        ((hK.2.1 ω).differentiable (by simp) 0)]
      ring
    have hi₁ := (hK.horizontalDerivative i).integrable_mul (hg.integrable_mul hf.1)
    have hi₂ := hK.integrable_mul ((hg.horizontalDerivative i).integrable_mul hf.1)
    rw [hsplit, integral_add hi₁ hi₂] at hp
    have heq : (∫ ω, (g ω * Df ω i + f ω * horizontalDerivative i g ω) * K ω ∂Q) =
        (∫ ω, Df ω i * (g ω * K ω) ∂Q) +
          ∫ ω, (f ω * horizontalDerivative i g ω) * K ω ∂Q := by
      rw [← integral_add ((hg.mul hK).integrable_mul (hf.2.1 i)) hi₂]
      congr 1
      funext ω
      ring
    rw [heq]
    linarith only [hp]
  refine ⟨hg.integrable_mul hf.1, hgi, fun i F G hFs hG => ?_⟩
  have h := Calculus.integral_chain_smooth hQ (g := id) contDiff_id (L := 1)
    (fun x => by simp) (hfm.mul hg.1) (hg.integrable_mul hf.1)
    (((hg.1.mul ((measurable_pi_apply i).comp hDfm)).add
      (hfm.mul (hg.measurable_derivative i)))) (hgi i) i (hcore i) hFs hG
  simpa only [id_eq, deriv_id, one_mul, Function.comp_def] using! h

end EinsteinRelation
