import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Euclidean bounds from coordinate moments

Source: `paper/main.tex:953–963`. The derivative corrections are finite sums
of scalar conditional averages. This estimate retains Euclidean norms when
combining their coordinate bounds, including infinite moments.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Coordinate moment bounds control the Euclidean moment without a moment
finiteness assumption. Source: `paper/main.tex:953–963`. -/
theorem eLpNorm_toLp_le_sum_coordinates {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (F : Ω → Fin d → ℝ) (hF : Measurable F) :
    eLpNorm (fun ω => (WithLp.toLp 2 (F ω) : EuclideanSpace ℝ (Fin d))) p μ ≤
      ∑ j : Fin d, eLpNorm (fun ω => F ω j) p μ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hdecomp (ω : Ω) : (WithLp.toLp 2 (F ω) : EuclideanSpace ℝ (Fin d)) =
      ∑ j : Fin d, F ω j • b j := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (b.sum_repr (WithLp.toLp 2 (F ω))).symm
  have hmeas (j : Fin d) : Measurable (fun ω => F ω j) :=
    (measurable_pi_apply j).comp hF
  have hterm (j : Fin d) :
      eLpNorm (fun ω => F ω j • b j) p μ ≤ eLpNorm (fun ω => F ω j) p μ := by
    apply eLpNorm_mono
    intro ω
    simp only [norm_smul, b.norm_eq_one, mul_one, le_refl]
  have hfun : (fun ω => (WithLp.toLp 2 (F ω) : EuclideanSpace ℝ (Fin d))) =
      ∑ j : Fin d, fun ω => F ω j • b j := by
    funext ω
    simpa only [Finset.sum_apply] using hdecomp ω
  rw [hfun]
  exact (eLpNorm_sum_le
    (fun j _ => ((hmeas j).smul_const (b j)).aestronglyMeasurable) hp).trans
      (Finset.sum_le_sum fun j _ => hterm j)

end EinsteinRelation.Correctors
