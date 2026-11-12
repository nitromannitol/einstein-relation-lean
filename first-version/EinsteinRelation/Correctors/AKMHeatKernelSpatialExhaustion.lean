import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Exhaustion by Euclidean spatial balls

Source: AKM (E.1)–(E.2), p. 499; `paper/main.tex:821–838`.
Compact tests and local integrability pass from an exhausting sequence
of balls to the whole coordinate space.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Every compact set lies in one of the integer-radius Euclidean balls. -/
theorem akm_compact_subset_originBall {d : ℕ} {s : Set (Vec d)} (hs : IsCompact s) :
    ∃ n : ℕ, s ⊆ originBall d (n + 1 : ℝ) := by
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  obtain ⟨R, hR⟩ := (hs.image hc).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, fun x hx => ?_⟩
  exact lt_of_le_of_lt (hR ⟨x, hx, rfl⟩) (by linarith)

private theorem locallyIntegrableOn_univ_of_originBall {d : ℕ} {f : Vec d → ℝ}
    (h : ∀ n : ℕ, LocallyIntegrableOn f (originBall d (n + 1 : ℝ)) volume) :
    LocallyIntegrableOn f Set.univ volume := by
  apply locallyIntegrableOn_univ.mpr
  apply locallyIntegrable_iff.mpr
  intro s hs
  obtain ⟨n, hn⟩ := akm_compact_subset_originBall hs
  exact (h n).integrableOn_compact_subset hn hs

/-- Weak gradients on exhausting Euclidean balls give a whole-space weak gradient.
Source: AKM (E.2), p. 499; `paper/main.tex:821–838`. -/
theorem akm_hasWeakGradient_univ_of_originBall {d : ℕ}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (h : ∀ n : ℕ, HasWeakGradient (originBall d (n + 1 : ℝ)) f G) :
    HasWeakGradient Set.univ f G := by
  intro j
  refine ⟨locallyIntegrableOn_univ_of_originBall (fun n => (h n j).1),
    locallyIntegrableOn_univ_of_originBall (fun n => (h n j).2.1), ?_⟩
  intro φ hφ
  obtain ⟨n, hn⟩ := akm_compact_subset_originBall hφ.2.1
  have heq := (h n j).2.2 φ ⟨hφ.1, hφ.2.1, hn⟩
  have hl : (∫ x in originBall d (n + 1 : ℝ), f x * coordinateDerivative j φ x) =
      ∫ x, f x * coordinateDerivative j φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport φ := fun hx' => hx (hn hx')
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs,
      ContinuousLinearMap.zero_apply, mul_zero]
  have hr : (∫ x in originBall d (n + 1 : ℝ), G x j * φ x) =
      ∫ x, G x j * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : φ x = 0 := by
      by_contra hz
      exact hx (hn (subset_tsupport φ hz))
    rw [hz, mul_zero]
  simpa only [Measure.restrict_univ, hl, hr] using heq

end EinsteinRelation.Correctors
