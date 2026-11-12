import EinsteinRelation.Correctors.PoissonLiftEllipticity

/-! Source: `paper/main.tex:735-739`. A measurable bounded normalized
source defines an actual coefficient field satisfying the GT hypotheses. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Every entry of the lifted matrix is measurable in a measurable source. -/
theorem measurable_poissonLiftMatrix {d n : ℕ} (F : Vec n → Vec d)
    (hF : Measurable F) :
    ∀ i j, Measurable (fun x => poissonLiftMatrix (F x) i j) := by
  intro i j
  have hc (k : Fin d) : Measurable (fun x => F x k) :=
    (measurable_pi_apply k).comp hF
  refine Fin.cases ?_ (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · change Measurable (fun x => 1 + euclideanSq (F x))
      apply measurable_const.add
      unfold euclideanSq dot
      exact Finset.measurable_sum _ (fun k _ => (hc k).mul (hc k))
    · simpa only [poissonLiftMatrix_zero_succ] using (hc l).neg
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [poissonLiftMatrix_succ_zero] using (hc k).neg
    · simp only [poissonLiftMatrix_succ_succ]
      exact measurable_const

/-- The normalized lift satisfies the full measurable GT ellipticity
contract on every domain, with constants depending only on the dimension. -/
theorem poissonLiftMatrix_ellipticBound {d : ℕ} (U : Set (Vec (d + 1)))
    (F : Vec (d + 1) → Vec d) (hF : Measurable F)
    (hFn : ∀ x ∈ U, euclideanNorm (F x) ≤ 1) :
    EllipticBound U (fun x => poissonLiftMatrix (F x))
      (1 / 4) (2 * ((d : ℝ) + 1)) := by
  refine ⟨measurable_poissonLiftMatrix F hF, fun x hx => ?_⟩
  obtain ⟨hcoercive, hbound⟩ := poissonLiftMatrix_bounds (F x) (hFn x hx)
  refine ⟨hcoercive, ?_⟩
  simpa only [sq_abs] using hbound

end EinsteinRelation.Correctors
