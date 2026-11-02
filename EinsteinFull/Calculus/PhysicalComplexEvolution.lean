import EinsteinFull.Frozen.PhysicalH1Graph
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull
open EinsteinRelation

/-- The full weak graph on complex L2(dx) of the physical operator
`(1/2) div(a grad) + zeta (a e_i).grad`, paper/main.tex:707–713.
The coefficient is the actual spatial matrix field. This definition contains
no existence, regularity, locality or weighted estimate. -/
def IsPhysicalComplexGeneratorPair {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) : Prop :=
  ∃ Gf : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    IsPhysicalH1Graph volume (Or.inl rfl) f Gf ∧
    ∀ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v Gv →
      (∫ x, g x * v x) =
        -(1 / 2 : ℂ) * (∫ x,
          ∑ j, ∑ k, (a x j k : ℂ) * Gf k x * Gv j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * Gf j x) * v x)

/-- The physical bilinear transpose graph, without complex conjugation.
The drift is in divergence form: `-zeta div(a e_i f)`. -/
def IsPhysicalComplexTransposeGeneratorPair {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) : Prop :=
  ∃ Gf : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    IsPhysicalH1Graph volume (Or.inl rfl) f Gf ∧
    ∀ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v Gv →
      (∫ x, g x * v x) =
        -(1 / 2 : ℂ) * (∫ x,
          ∑ j, ∑ k, (a x k j : ℂ) * Gf k x * Gv j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * Gv j x))

/-- C0 evolution on physical L2(dx), identified by equality of its complete
infinitesimal-generator graph with the actual physical weak graph. -/
def IsPhysicalComplexSemigroup {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) : Prop :=
  P 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure (Vec d))) ∧
  (∀ s t : ℝ≥0, P (s + t) = (P s).comp (P t)) ∧
  (∀ f : Lp ℂ 2 (volume : Measure (Vec d)), Continuous (fun t : ℝ≥0 => P t f)) ∧
  ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsPhysicalComplexGeneratorPair a i ζ f g

/-- The physical C0 transpose evolution, with its complete weak generator
graph and the bilinear dx pairing. No analytic or kernel estimate is assumed. -/
def IsPhysicalComplexTransposeSemigroup {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) : Prop :=
  Pdag 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure (Vec d))) ∧
  (∀ s t : ℝ≥0, Pdag (s + t) = (Pdag s).comp (Pdag t)) ∧
  (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    Continuous (fun t : ℝ≥0 => Pdag t f)) ∧
  (∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (Pdag t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔
      IsPhysicalComplexTransposeGeneratorPair a i ζ f g) ∧
  ∀ (t : ℝ≥0) (f g : Lp ℂ 2 (volume : Measure (Vec d))),
    (∫ x, P t f x * g x) = ∫ x, f x * Pdag t g x

/-- The literal physical dx integral-kernel relation for the forward and
bilinear transpose evolutions. Positive-time actions have genuine Bochner
integrability for all L2 data, and equality of representatives is a.e.
Swapping spatial coordinates gives the transpose kernel, without conjugation.
A smooth representative and all Gaussian bounds remain construction goals. -/
def IsPhysicalComplexKernel {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K : ℝ≥0 → Vec d → Vec d → ℂ) : Prop :=
  ∀ (t : ℝ≥0), 0 < t → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ((∀ᵐ x ∂volume, Integrable (fun y => K t x y * f y)) ∧
      (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K t x y * f y) ∧
    ((∀ᵐ x ∂volume, Integrable (fun y => K t y x * f y)) ∧
      (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K t y x * f y)

/-- For symmetric coefficients the zero-force physical weak graphs coincide. -/
theorem physicalComplexGeneratorPair_zero_iff {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ (x : Vec d) (j k : Fin d), a x j k = a x k j)
    (i : Fin d) (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexGeneratorPair a i 0 f g ↔
      IsPhysicalComplexTransposeGeneratorPair a i 0 f g := by
  simp only [IsPhysicalComplexGeneratorPair, IsPhysicalComplexTransposeGeneratorPair,
    zero_mul, add_zero, ha]

/-- The kernel relation preserves the literal spatial swap under transposition. -/
theorem IsPhysicalComplexKernel.transpose {d : ℕ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {K : ℝ≥0 → Vec d → Vec d → ℂ} (hK : IsPhysicalComplexKernel P Pdag K) :
    IsPhysicalComplexKernel Pdag P (fun t x y => K t y x) := by
  intro t ht f
  exact (hK t ht f).symm

end EinsteinFull
