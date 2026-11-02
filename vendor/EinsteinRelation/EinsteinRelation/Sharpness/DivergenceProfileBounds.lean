import EinsteinRelation.Sharpness.ScaledSeedDerivatives
import EinsteinRelation.TimeChange.Pairing
import EinsteinRelation.Sharpness.DivergenceProfile
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Pi
open MeasureTheory
namespace EinsteinRelation.Sharpness
/-- Compact box of finite gradient/Hessian coordinates. The auxiliary parameters carry product
supremum norms; source spatial estimates still use `euclideanNorm`. -/
def coefficientJetBox (d : ℕ) (M : ℝ) : Set (Vec d × (Fin d → Fin d → ℝ)) :=
  Set.Icc ((fun _ => -(1/4 : ℝ)), (fun _ _ => -M)) ((fun _ => (1/4 : ℝ)), (fun _ _ => M))

/-- Source main.tex1218–1231: the actual rational divergence profile is bounded and Lipschitz
on every compact admissible finite-jet box. Constants precede all parameter samples. -/
theorem exists_coefficientDivergenceProfile_bound_and_lipschitz (d : ℕ) (i : Fin d) (M : ℝ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      (∀ z ∈ coefficientJetBox d M, |coefficientDivergenceProfile i z| ≤ C) ∧
      ∀ z ∈ coefficientJetBox d M, ∀ w ∈ coefficientJetBox d M,
        |coefficientDivergenceProfile i z - coefficientDivergenceProfile i w| ≤ L * ‖z-w‖ := by
  have hcompact : IsCompact (coefficientJetBox d M) := isCompact_Icc
  have hj (z : Vec d × (Fin d → Fin d → ℝ)) (hz : z ∈ coefficientJetBox d M) :
      1 + z.1 i ≠ 0 := by
    have hlow : -(1/4 : ℝ) ≤ z.1 i := hz.1.1 i
    linarith
  have hcont : ContinuousOn (coefficientDivergenceProfile i) (coefficientJetBox d M) :=
    fun z hz => ((contDiffAt_coefficientDivergenceProfile i z (hj z hz)).continuousAt).continuousWithinAt
  have hderiv : ContinuousOn (fderiv ℝ (coefficientDivergenceProfile i)) (coefficientJetBox d M) :=
    fun z hz => ((contDiffAt_coefficientDivergenceProfile i z (hj z hz)).continuousAt_fderiv
      (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  obtain ⟨L,hL⟩ := hcompact.exists_bound_of_continuousOn hderiv
  refine ⟨max C 0, max L 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro z hz
    exact (hC z hz).trans (le_max_left _ _)
  · intro z hz w hw
    have hd : ∀ z ∈ coefficientJetBox d M, DifferentiableAt ℝ (coefficientDivergenceProfile i) z :=
      fun z hz => (contDiffAt_coefficientDivergenceProfile i z (hj z hz)).differentiableAt
        (by simp)
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hd hL
      (convex_Icc _ _) hw hz
    change |coefficientDivergenceProfile i z - coefficientDivergenceProfile i w| ≤ _
    exact (show |coefficientDivergenceProfile i z - coefficientDivergenceProfile i w| ≤
        L * ‖z-w‖ from hh).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
end EinsteinRelation.Sharpness
namespace EinsteinRelation.Sharpness
/-- One compact finite-jet box contains all actual scaled samples at every point, for the SAME
supplied admissible scale. Source main.tex1212–1231. The constant precedes all samples. -/
theorem exists_uniform_scaled_seedField_jet_box {d : ℕ} (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (W : NoiseSample d) (x : Vec d),
      (gradient (fun y => ε * seedField d W y) x,
        fun m n => coordinateDerivative m (coordinateDerivative n
          (fun y => ε * seedField d W y)) x) ∈ coefficientJetBox d M := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_scaled_seedField_third_jet_bound d ε
  refine ⟨M,hM,fun W x => ?_⟩
  have hc (k : Fin d) : |gradient (fun y => ε * seedField d W y) x k| ≤ (1/4 : ℝ) := by
    have h := jacobianFactor_bounds k _ (hgrad W x)
    unfold jacobianFactor at h
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  change ((∀ k : Fin d, -(1/4 : ℝ) ≤ gradient (fun y => ε * seedField d W y) x k) ∧
    ∀ m n : Fin d, -M ≤ coordinateDerivative m (coordinateDerivative n
      (fun y => ε * seedField d W y)) x) ∧
    ((∀ k : Fin d, gradient (fun y => ε * seedField d W y) x k ≤ (1/4 : ℝ)) ∧
    ∀ m n : Fin d, coordinateDerivative m (coordinateDerivative n
      (fun y => ε * seedField d W y)) x ≤ M)
  exact ⟨⟨fun k => (abs_le.mp (hc k)).1,
    fun m n => (abs_le.mp ((hb W x).2.2.1 m n)).1⟩,
    ⟨fun k => (abs_le.mp (hc k)).2,
    fun m n => (abs_le.mp ((hb W x).2.2.1 m n)).2⟩⟩
end EinsteinRelation.Sharpness
