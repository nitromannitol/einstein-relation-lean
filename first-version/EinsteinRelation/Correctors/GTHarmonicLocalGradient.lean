import EinsteinRelation.Correctors.InteriorGradientTransfer
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# Local gradient bounds from the three GT inputs

Source: `paper/main.tex:735-739`. Qualitative interior regularity supplies
a representative on the doubled unit ball. Local boundedness controls its
values, and GT 8.32 controls its gradient with a constant chosen before the
solution and its finite gradient Hölder bound.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

private theorem isOpen_ball {d : ℕ} (R : ℝ) :
    IsOpen (ball (0 : Vec d) R) := by
  unfold ball euclideanNorm euclideanSq dot
  exact isOpen_lt (by fun_prop) continuous_const

/-- The local harmonic gradient bound needs no quantitative version of
GT (8.91). The constant is independent of the solution's Hölder norm.
The estimate is on the original weak gradient almost everywhere. -/
theorem harmonic_local_gradient_bound_of_GT
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) (hd : 2 ≤ d) (lam Λ K α : ℝ)
    (hlam : 0 < lam) (hΛ : 0 < Λ) (hK : 0 < K)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d),
      EllipticBound (ball 0 4) a lam Λ →
      (∀ i j, HolderBound (ball 0 4) α (fun x => a x i j) K) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 4) a u g →
        ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
          euclideanNorm (g x) ≤ C *
            Real.sqrt (∫ z in ball 0 4, |u z| ^ 2 ∂volume) := by
  obtain ⟨CB, hCB, hB⟩ := h817 d hd lam Λ 2 hlam hΛ (by norm_num)
  obtain ⟨CS, hCS, hS⟩ := h832 d hd lam K α 1 hlam hK hα hα1 zero_lt_one
  let A : ℝ := CB * (2 : ℝ) ^ (-(d : ℝ) / 2)
  have hA : 0 < A := mul_pos hCB (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨CS * A, mul_pos hCS hA, ?_⟩
  intro a ha hholder u g hw
  have h24 : ball (0 : Vec d) 2 ⊆ ball 0 4 := by
    intro x hx
    exact (show euclideanNorm (x - 0) < 2 from hx).trans (by norm_num)
  have h12 : ball (0 : Vec d) 1 ⊆ ball 0 2 := by
    intro x hx
    exact (show euclideanNorm (x - 0) < 1 from hx).trans (by norm_num)
  obtain ⟨v, h, hreg, hv, hh⟩ := h836 d hd lam K α 2
    hlam hK hα hα1 (by norm_num) a
    (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      fun x hx => (ha.2 x hx).1)
    (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hholder)
    u g (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hw)
  have hweak := weakSolution_congr_ae hv hh
    (weakSolution_restrict_subset (isOpen_ball 4).measurableSet h24 hw)
  have hb : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
      |u x| ≤ A * Real.sqrt (∫ z in ball 0 4, |u z| ^ 2 ∂volume) := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num, Real.rpow_two,
      Real.sqrt_eq_rpow, A] using
      hB (ball 0 4) (isOpen_ball 4) a ha u g hw 0 2 (by norm_num)
        (by norm_num) (by norm_num at *; exact hw.1)
  have hb' : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
      |v x| ≤ A * Real.sqrt (∫ z in ball 0 4, |u z| ^ 2 ∂volume) := by
    filter_upwards [hv, hb] with x hx hbx
    simpa only [hx] using hbx
  have hcont : ContinuousOn v (ball (0 : Vec d) 2) :=
    fun x hx => (hreg.1 x hx).continuousAt.continuousWithinAt
  have hpoint := abs_le_on_open_of_ae (isOpen_ball 2) hcont hb'
  have hgrad : ∀ x ∈ ball (0 : Vec d) 1,
      euclideanNorm (h x) ≤ CS *
        (A * Real.sqrt (∫ z in ball 0 4, |u z| ^ 2 ∂volume)) := by
    apply hS a
    · simpa only [mul_one] using fun x hx => (ha.2 x (h24 hx)).1
    · intro i j
      obtain ⟨S, H, hS0, hH0, hsum, hsup, hhold⟩ := hholder i j
      simpa only [mul_one] using
        (show HolderBound (ball (0 : Vec d) 2) α (fun x => a x i j) K from
          ⟨S, H, hS0, hH0, hsum, fun x hx => hsup x (h24 hx),
            fun x hx y hy => hhold x (h24 hx) y (h24 hy)⟩)
    · simpa only [mul_one] using hweak
    · simpa only [mul_one] using hreg
    · positivity
    · simpa only [mul_one] using hpoint
  have hh' := hh.filter_mono (ae_mono (Measure.restrict_mono_set volume h12))
  filter_upwards [hh', ae_restrict_mem (isOpen_ball 1).measurableSet] with x hx hxb
  rw [← hx, mul_assoc]
  exact hgrad x hxb

end EinsteinRelation.Correctors
