import EinsteinRelation.Correctors.PoissonLiftWeakSolution
import EinsteinRelation.Correctors.PoissonLiftHolder
import EinsteinRelation.Correctors.ClippedSourceHolder
import EinsteinRelation.Correctors.PoissonLiftContinuousSlice
import EinsteinRelation.Correctors.InteriorGradientTransfer

/-! Source: `paper/main.tex:735-743`. Hölder divergence sources admit
continuous Poisson potential versions using the existing homogeneous GT
input and the explicit dimension lift. No inhomogeneous Schauder theorem
is introduced as an additional external assumption. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The frozen homogeneous GT regularity input suffices for continuity
of an actual weak Poisson potential with a bounded Hölder source. -/
theorem exists_continuousOn_poisson_potential_of_gt
    (h836 : InteriorRegularRepresentative) {d : ℕ} (hd : 2 ≤ d)
    (u : Vec d → ℝ) (g F : Vec d → Vec d)
    (hw : HasWeakGradient Set.univ u g)
    (hJ : HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0))
    (hFmeas : Measurable F)
    (hu : MemLp u 2 (volume.restrict (ball 0 1)))
    (hg : MemLp g 2 (volume.restrict (ball 0 1)))
    (K : ℝ) (hF : ∀ j, HolderBound (ball 0 1) (1 / 2) (fun x => F x j) K) :
    ∃ v : Vec d → ℝ, ContinuousOn v (ball 0 (1 / 4)) ∧
      u =ᵐ[volume.restrict (ball 0 (1 / 4))] v := by
  let M : ℝ := ((d : ℝ) + 1) * (|K| + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hFn : ∀ x ∈ ball (0 : Vec d) 1, euclideanNorm (F x) ≤ M := by
    intro x hx
    have hn : ‖F x‖ ≤ |K| + 1 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ |K| + 1)).mpr
      intro j
      obtain ⟨S, H, _, hH, hSH, hs, _⟩ := hF j
      rw [Real.norm_eq_abs]
      exact (hs x hx).trans (by linarith [le_abs_self K])
    exact (euclideanNorm_le_dimension_mul_norm (F x)).trans
      (mul_le_mul_of_nonneg_left hn (by positivity))
  obtain ⟨C, hC⟩ := exists_holderBound_clippedPoissonSource_lift F (1 / 2) K M
    (by norm_num) hM hFn hF
  obtain ⟨D, hD, hDholder⟩ := exists_holderBound_poissonLiftMatrix
    (ball (0 : Vec (d + 1)) 1) (1 / 2) C
    (fun x => clippedPoissonSource F M (poissonLiftBase x)) hC
  have hbase : Measurable (poissonLiftBase : Vec (d + 1) → Vec d) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply j.succ)
  have hell := poissonLiftMatrix_ellipticBound (ball (0 : Vec (d + 1)) 1)
    (fun x => clippedPoissonSource F M (poissonLiftBase x))
    ((measurable_clippedPoissonSource F hFmeas M).comp hbase)
    (fun x _ => euclideanNorm_clippedPoissonSource_le F M hM _)
  have hsol := weakSolution_poissonLift u g F hw hJ hFmeas M hM
    (by filter_upwards [ae_restrict_mem (by
          unfold ball euclideanNorm euclideanSq dot
          exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
        exact hFn x hx) hu hg
  obtain ⟨v, h, hreg, hveq, _⟩ := h836 (d + 1) (by omega)
    (1 / 4) D (1 / 2) (1 / 2) (by norm_num) hD (by norm_num) (by norm_num)
    (by norm_num) (fun x => poissonLiftMatrix (clippedPoissonSource F M (poissonLiftBase x)))
    (by simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num] using fun x hx => (hell.2 x hx).1)
    (by simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num] using hDholder)
    _ _ (by simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num] using hsol)
  exact exists_continuousOn_of_poissonLift_representative u M v
    (fun x hx => (hreg.1 x hx).continuousAt.continuousWithinAt) hveq

end EinsteinRelation.Correctors
