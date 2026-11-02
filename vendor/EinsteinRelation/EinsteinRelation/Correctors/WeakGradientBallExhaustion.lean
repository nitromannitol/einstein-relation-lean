import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.BallPoincareTransfer
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory
open Set
open Filter

namespace EinsteinRelation.Correctors
open External.AKM

/-- Weak gradients are local on the increasing Euclidean-ball exhaustion;
source `paper/main.tex:693-698`. -/
theorem hasWeakGradient_univ_of_balls {d : ℕ}
    (u : Vec d → ℝ) (g : Vec d → Vec d)
    (h : ∀ n : ℕ, HasWeakGradient (ball 0 ((n : ℝ) + 1)) u g) :
    HasWeakGradient Set.univ u g := by
  have hopen (n : ℕ) : IsOpen (ball (0 : Vec d) ((n : ℝ) + 1)) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hcover (x : Vec d) : ∃ n : ℕ, x ∈ ball (0 : Vec d) ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - 0))
    exact ⟨n, lt_trans hn (by linarith)⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    obtain ⟨n, hn⟩ := hcover x
    simpa only [nhdsWithin_univ, nhdsWithin_eq_nhds.mpr ((hopen n).mem_nhds hn)] using (h n i).1 x hn
  · intro x _
    obtain ⟨n, hn⟩ := hcover x
    simpa only [nhdsWithin_univ, nhdsWithin_eq_nhds.mpr ((hopen n).mem_nhds hn)] using (h n i).2.1 x hn
  · intro φ hφ
    have hc := hφ.2.1.isCompact.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
    obtain ⟨B, _, hB⟩ := hc.isBounded.exists_pos_norm_le
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have hs : tsupport φ ⊆ ball (0 : Vec d) ((n : ℝ) + 1) := by
      intro x hx
      have hb := hB (WithLp.toLp 2 x) ⟨x, hx, rfl⟩
      change euclideanNorm (x - 0) < (n : ℝ) + 1
      rw [sub_zero, TimeChange.euclideanNorm_eq_norm_toLp]
      exact lt_of_le_of_lt hb (by linarith)
    have ht := (h n i).2.2 φ ⟨hφ.1, hφ.2.1, hs⟩
    have hleft : (∫ x in ball (0 : Vec d) ((n : ℝ) + 1),
        u x * coordinateDerivative i φ x) = ∫ x, u x * coordinateDerivative i φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz := fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht))
      simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply, mul_zero]
    have hright : (∫ x in ball (0 : Vec d) ((n : ℝ) + 1), g x i * φ x) =
        ∫ x, g x i * φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz := (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hs ht))).self_of_nhds
      simp only [hz, Pi.zero_apply, mul_zero]
    simpa only [Measure.restrict_univ, hleft, hright] using ht

end EinsteinRelation.Correctors
