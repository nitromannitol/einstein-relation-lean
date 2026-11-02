import EinsteinFull.Blueprint.Foundation.node_p_u3A_gauge_u23_closed_u2D_form

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:gauge#holomorphic`, `paper/main.tex:611`.
The entire family is the actual bilinear physical H1 form. Its linear
coefficient is the half column divergence. The structural form bounds use
integration by parts, rather than a bound depending on coefficient derivatives.
There is no claim here about stationary Lp realizations. -/
def node_p_u3A_gauge_u23_holomorphicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ), ∃ C : ℝ, 0 < C ∧
    ∀ (i : Fin d) (B : ℝ), 0 ≤ B → ∀ a : Vec d → Mat d,
      ∀ ha : IsElliptic Λ a, IsOperatorLipschitz B a →
      ∀ haSmooth : ∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k),
      let hcoef : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume :=
        fun j k => memLp_complex_elliptic_entry volume a Λ
          (lt_of_lt_of_le zero_lt_one hΛ) ha
          (fun j k => (haSmooth j k).continuous) j k
      ∀ s : ℝ, 0 ≤ s →
      ∀ (u v : Lp ℂ 2 (volume : Measure (Vec d)))
        (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) u G →
        IsPhysicalH1Graph volume (Or.inl rfl) v H →
        let linear : ℂ := ∫ x : Vec d,
          (((1 / 2 : ℝ) * ∑ j : Fin d,
            coordinateDerivative j (fun y => a y j i) x : ℝ) : ℂ) * u x * v x
        let quadratic : ℂ := (1 / 2 : ℂ) * ∫ x : Vec d, (a x i i : ℂ) * u x * v x
        Differentiable ℂ (fun ζ : ℂ => physicalBilinearForm volume a hcoef i s ζ u G v H) ∧
        ∀ ζ : ℂ,
          physicalBilinearForm volume a hcoef i s ζ u G v H =
            physicalBilinearForm volume a hcoef i s 0 u G v H +
              ζ * linear + ζ ^ 2 * quadratic ∧
          ‖ζ * linear‖ ≤ C * ‖ζ‖ *
            (‖u‖ * Real.sqrt (∑ j : Fin d, ‖H j‖ ^ 2) +
              ‖v‖ * Real.sqrt (∑ j : Fin d, ‖G j‖ ^ 2)) ∧
          ‖ζ ^ 2 * quadratic‖ ≤ C * ‖ζ‖ ^ 2 * ‖u‖ * ‖v‖

end EinsteinFull.Blueprint
