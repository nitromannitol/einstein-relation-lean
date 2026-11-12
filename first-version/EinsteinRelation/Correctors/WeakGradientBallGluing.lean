import EinsteinRelation.Correctors.LocalWeakGradientUniqueness
import EinsteinRelation.Correctors.AKMHeatKernelSpatialExhaustion
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.SpatialWeakCongruence

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Compatible local weak gradients glue to a whole-space gradient, without
requiring an independently chosen global representative.
Source: `paper/main.tex:798–810`; prescribed-time gradient recovery. -/
theorem exists_global_weakGradient_of_ball_gradients {d : ℕ} {u : Vec d → ℝ}
    (h : ∀ R : ℝ, 0 < R → ∃ G : Vec d → Vec d,
      HasWeakGradient (originBall d R) u G) :
    ∃ G : Vec d → Vec d, HasWeakGradient Set.univ u G := by
  classical
  let U : ℕ → Set (Vec d) := fun n => originBall d (n + 1 : ℝ)
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hopen n : IsOpen (U n) := isOpen_lt hnorm continuous_const
  choose G hG using fun n : ℕ => h (n+1) (by positivity)
  have hex (x : Vec d) : ∃ n : ℕ, x ∈ U n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm x)
    exact ⟨n, hn.trans (by change (n : ℝ) < n+1; linarith)⟩
  let N : Vec d → ℕ := fun x => Nat.find (hex x)
  let H : Vec d → Vec d := fun x => G (N x) x
  have hagree (n m : ℕ) : ∀ᵐ x ∂volume, x ∈ U n ∩ U m → G n x = G m x := by
    have hi (i : Fin d) := weakPartialDerivative_ae_eq_on_open
      ((hopen n).inter (hopen m))
      (hasWeakGradient_mono Set.inter_subset_left (hG n) i)
      (hasWeakGradient_mono Set.inter_subset_right (hG m) i)
    have he : G n =ᵐ[volume.restrict (U n ∩ U m)] G m := by
      filter_upwards [ae_all_iff.mpr hi] with x hx
      exact funext hx
    exact (ae_restrict_iff' ((hopen n).inter (hopen m)).measurableSet).mp he
  refine ⟨H, akm_hasWeakGradient_univ_of_originBall fun n i => ?_⟩
  have he : H =ᵐ[volume.restrict (U n)] G n := by
    apply (ae_restrict_iff' (hopen n).measurableSet).mpr
    filter_upwards [ae_all_iff.mpr (fun m => hagree m n)] with x hx
    intro hxn
    exact hx (N x) ⟨Nat.find_spec (hex x),hxn⟩
  exact hasWeakPartialDerivative_congr_ae (hopen n) (hG n i)
    Filter.EventuallyEq.rfl (he.symm.mono fun x hx => congrFun hx i)

end EinsteinRelation.Correctors
