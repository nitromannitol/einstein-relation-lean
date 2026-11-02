import EinsteinFull.Calculus.PhysicalDomainSupport
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Complex-force polynomial structure of the actual bilinear form.

Quadratic interpolation at 0, 1 and -1 proves entire dependence on the full
L2 domain. Identifying its linear coefficient with the drift remains separate.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The actual shifted-gradient form is quadratic in its complex force. -/
theorem physicalBilinearForm_quadratic {d : ℕ} (m : Measure (Vec d))
    (a : Vec d → Mat d) (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ m)
    (i : Fin d) (s : ℝ) (u v : Lp ℂ 2 m) (G H : Fin d → Lp ℂ 2 m) (ζ : ℂ) :
    let F := fun z : ℂ => physicalBilinearForm m a ha i s z u G v H
    F ζ = F 0 + ζ * ((F 1 - F (-1)) / 2) +
      ζ ^ 2 * ((F 1 + F (-1)) / 2 - F 0) := by
  let E (z : ℂ) (x : Vec d) := ∑ j : Fin d, ∑ k : Fin d,
    (G j x - z * (unitVector i j : ℂ) * u x) * (a x j k : ℂ) *
      (H k x - z * (unitVector i k : ℂ) * v x)
  have hE (z : ℂ) (x : Vec d) :
      E z x = E 0 x + z * ((E 1 x - E (-1) x) / 2) +
        z ^ 2 * ((E 1 x + E (-1) x) / 2 - E 0 x) := by
    let t (z : ℂ) (j k : Fin d) :=
      (G j x - z * (unitVector i j : ℂ) * u x) * (a x j k : ℂ) *
        (H k x - z * (unitVector i k : ℂ) * v x)
    calc
      E z x = ∑ j : Fin d, ∑ k : Fin d,
          (t 0 j k + z * ((t 1 j k - t (-1) j k) / 2) +
            z ^ 2 * ((t 1 j k + t (-1) j k) / 2 - t 0 j k)) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        dsimp [t]
        ring
      _ = _ := by
        dsimp only [E, t]
        simp only [div_eq_mul_inv, mul_sub, mul_add, sub_mul, add_mul,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  let B (z : ℂ) (x : Vec d) := (s : ℂ) * (u x * v x) + (1 / 2 : ℂ) * E z x
  have hB (z : ℂ) : Integrable (B z) m :=
    ((Lp.memLp u).integrable_mul (Lp.memLp v)).const_mul _ |>.add
      ((physicalBilinearForm_integrable m a ha i z u v G H).2.const_mul _)
  have hF (z : ℂ) : physicalBilinearForm m a ha i s z u G v H = ∫ x, B z x ∂m := by
    have hm : Integrable (fun x => (s : ℂ) * (u x * v x)) m :=
      ((Lp.memLp u).integrable_mul (Lp.memLp v)).const_mul _
    have he : Integrable (fun x => (1 / 2 : ℂ) * E z x) m :=
      (physicalBilinearForm_integrable m a ha i z u v G H).2.const_mul _
    change (s : ℂ) * (∫ x, u x * v x ∂m) + (1 / 2 : ℂ) * (∫ x, E z x ∂m) =
      ∫ x, (s : ℂ) * (u x * v x) + (1 / 2 : ℂ) * E z x ∂m
    rw [integral_add hm he, integral_const_mul, integral_const_mul]
  have hpoint (x : Vec d) : B ζ x = B 0 x + ζ * ((B 1 x - B (-1) x) / 2) +
      ζ ^ 2 * ((B 1 x + B (-1) x) / 2 - B 0 x) := by
    dsimp only [B]
    rw [hE ζ x]
    ring
  have hL : Integrable (fun x => (B 1 x - B (-1) x) / 2) m :=
    ((hB 1).sub (hB (-1))).div_const (2 : ℂ)
  have hP : Integrable (fun x => (B 1 x + B (-1) x) / 2) m :=
    ((hB 1).add (hB (-1))).div_const (2 : ℂ)
  have hQ : Integrable (fun x => (B 1 x + B (-1) x) / 2 - B 0 x) m :=
    (((hB 1).add (hB (-1))).div_const (2 : ℂ)).sub (hB 0)
  have hLz : Integrable (fun x => ζ * ((B 1 x - B (-1) x) / 2)) m := hL.const_mul ζ
  have hQz : Integrable (fun x => ζ ^ 2 * ((B 1 x + B (-1) x) / 2 - B 0 x)) m :=
    hQ.const_mul (ζ ^ 2)
  have h0L : Integrable (fun x => B 0 x + ζ * ((B 1 x - B (-1) x) / 2)) m :=
    (hB 0).add hLz
  dsimp only
  simp only [hF]
  calc
    (∫ x, B ζ x ∂m) = ∫ x, B 0 x + ζ * ((B 1 x - B (-1) x) / 2) +
        ζ ^ 2 * ((B 1 x + B (-1) x) / 2 - B 0 x) ∂m :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_add h0L hQz,
        integral_add (hB 0) hLz, integral_const_mul, integral_const_mul,
        integral_div, integral_sub (hB 1) (hB (-1)),
        integral_sub hP (hB 0),
        integral_div, integral_add (hB 1) (hB (-1))]

/-- The actual physical bilinear form is entire on the full public L2 domain. -/
theorem physicalBilinearForm_differentiable {d : ℕ} (m : Measure (Vec d))
    (a : Vec d → Mat d) (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ m)
    (i : Fin d) (s : ℝ) (u v : Lp ℂ 2 m) (G H : Fin d → Lp ℂ 2 m) :
    Differentiable ℂ (fun ζ : ℂ => physicalBilinearForm m a ha i s ζ u G v H) := by
  have hfun := funext (physicalBilinearForm_quadratic m a ha i s u v G H)
  rw [hfun]
  exact ((differentiable_const _).add (differentiable_id.mul_const _)).add
    ((differentiable_id.pow 2).mul_const _)

end EinsteinFull
