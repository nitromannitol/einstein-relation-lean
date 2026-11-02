import EinsteinFull.Proofs.Gauge
import EinsteinFull.Frozen.PhysicalForceMeasure
import EinsteinFull.Frozen.PhysicalH1Graph
import EinsteinFull.Frozen.PhysicalBilinearForm
import EinsteinFull.Frozen.PhysicalGaugeMultiplier
import EinsteinFull.Calculus.PhysicalCoefficientSupport
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Complex.Basic

open scoped ENNReal
open MeasureTheory
namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Proposition 4.1 on full physical H1 domains. The closed graph assertions
are in the complete L2 product; ellipticity makes its graph norm equivalent to
the closed form norm. The complex continuation is bilinear. -/
theorem gauge (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (Λ B : ℝ)
    (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) (a : Vec d → Mat d)
    (ha : IsElliptic Λ a) (haLip : IsOperatorLipschitz B a)
    (haSmooth : ∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (lam s : ℝ) (hs : 0 ≤ s) :
    let hcoef : ∀ (m : Measure (Vec d)) (j k : Fin d),
      MemLp (fun x => (a x j k : ℂ)) ∞ m := fun m j k =>
        memLp_complex_elliptic_entry m a Λ (lt_of_lt_of_le zero_lt_one hΛ) ha
          (fun j k => (haSmooth j k).continuous) j k
    ∃ U : Lp ℂ 2 (physicalForceMeasure i lam) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)),
    (∀ f : Lp ℂ 2 (physicalForceMeasure i lam),
      (U f : Vec d → ℂ) =ᵐ[volume] physicalGaugeMultiplier i lam f) ∧
    IsClosed {p : Lp ℂ 2 (physicalForceMeasure i lam) ×
      (Fin d → Lp ℂ 2 (physicalForceMeasure i lam)) |
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) p.1 p.2} ∧
    IsClosed {p : Lp ℂ 2 (volume : Measure (Vec d)) ×
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) |
      IsPhysicalH1Graph volume (Or.inl rfl) p.1 p.2} ∧
    (∀ f : Lp ℂ 2 (physicalForceMeasure i lam),
      (∃ G, IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G) ↔
        ∃ H, IsPhysicalH1Graph volume (Or.inl rfl) (U f) H) ∧
    (∀ (f : Lp ℂ 2 (physicalForceMeasure i lam))
      (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam)),
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (U f) H ∧
        ∀ j : Fin d, (H j : Vec d → ℂ) =ᵐ[volume] fun x =>
          (Real.exp (lam * x i) : ℂ) * (G j x + (lam : ℂ) *
            (unitVector i j : ℂ) * f x)) ∧
    (∀ (f g : Lp ℂ 2 (physicalForceMeasure i lam))
      (G H : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
      (G' H' : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G →
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) g H →
      IsPhysicalH1Graph volume (Or.inl rfl) (U f) G' → IsPhysicalH1Graph volume (Or.inl rfl) (U g) H' →
      physicalBilinearForm (physicalForceMeasure i lam) a (hcoef _) i s 0
        f (fun j => G j) g (fun j => H j) =
      physicalBilinearForm volume a (hcoef _) i s (lam : ℂ)
        (U f) (fun j => G' j) (U g) (fun j => H' j)) ∧
    (∀ (a_minus : ℝ), 0 ≤ a_minus →
      (∀ (x ξ : Vec d), a_minus * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ)) →
      ∀ (u : Lp ℂ 2 (volume : Measure (Vec d)))
        (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) u G →
      (s + a_minus * lam ^ 2 / 2) * ‖u‖ ^ 2 +
        (a_minus / 2) * (∑ j : Fin d, ‖G j‖ ^ 2) ≤
      (physicalBilinearForm volume a (hcoef _) i s (lam : ℂ)
        (star u) (fun j => star (G j))
        u (fun j => G j)).re) ∧
    (∀ (u v : Lp ℂ 2 (volume : Measure (Vec d)))
      (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) u G → IsPhysicalH1Graph volume (Or.inl rfl) v H →
      Differentiable ℂ (fun ζ : ℂ =>
        physicalBilinearForm volume a (hcoef _) i s ζ u (fun j => G j) v (fun j => H j)) ∧
      ∀ ζ : ℂ, physicalBilinearForm volume a (hcoef _) i s ζ u (fun j => G j) v (fun j => H j) =
        physicalBilinearForm volume a (hcoef _) i s 0 u (fun j => G j) v (fun j => H j) +
        ζ * (∫ x : Vec d, (((1 / 2 : ℝ) * ∑ j : Fin d,
          coordinateDerivative j (fun y => a y j i) x : ℝ) : ℂ) * u x * v x) +
        (ζ ^ 2 / 2) * (∫ x : Vec d, (a x i i : ℂ) * u x * v x)) := by
  exact EinsteinFull.Proofs.gauge d hd i Λ B hΛ hB a ha haLip haSmooth lam s hs

end EinsteinFull.Frozen
