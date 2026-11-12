import EinsteinRelation.Correctors.PoissonRegularRepresentative
import EinsteinRelation.Correctors.HolderDilation
import EinsteinRelation.Correctors.RegularRepresentativeDilation
import EinsteinRelation.Correctors.LocalHolderMemLp
import EinsteinRelation.Correctors.SpatialWeakDilation

/-! Source: `paper/main.tex:735-743`. Spatial dilation applies the
unit-ball Poisson regularity argument on every positive Euclidean ball. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Homogeneous GT regularity yields continuous local versions of a
Poisson potential with locally Hölder divergence source on all scales. -/
theorem exists_continuousOn_poisson_potential_ball_of_gt
    (h836 : InteriorRegularRepresentative) {d : ℕ} (hd : 2 ≤ d)
    (u : Vec d → ℝ) (g F : Vec d → Vec d)
    (hw : HasWeakGradient Set.univ u g)
    (hJ : HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0))
    (hFm : Measurable F)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)))
    (hF : ∀ R : ℝ, 0 < R → ∃ K : ℝ, ∀ j,
      HolderBound (ball 0 R) (1 / 2) (fun x => F x j) K)
    (R : ℝ) (hR : 0 < R) :
    ∃ v : Vec d → ℝ, ContinuousOn v (ball 0 R) ∧
      u =ᵐ[volume.restrict (ball 0 R)] v := by
  let s : ℝ := 4 * R
  have hs : 0 < s := by dsimp [s]; positivity
  have hu' := memLp_two_on_euclidean_balls_dilation u hu s 1 hs
  have hg' := memLp_two_on_euclidean_balls_dilation g hg s s hs
  have hFl2 := memLp_on_euclidean_balls_of_holder_components F hFm hF
  have hw' := hasWeakGradient_dilation u g hu hg hw s 1 hs
  have hJ' := hasWeakDivergence_zero_dilation (fun x => g x - F x)
    (fun r hr => (hg r hr).sub (hFl2 r hr)) hJ s s hs
  obtain ⟨K, hK⟩ := hF s hs
  have hsc (j : Fin d) : ∃ C : ℝ, HolderBound (ball 0 1) (1 / 2)
      (fun x => (s • F (s • x)) j) C := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      exists_holderBound_half_dilation (fun x => F x j) s s 1 s K hs
        (by norm_num) (by simp) (hK j)
  choose C hC using hsc
  let D : ℝ := ∑ j : Fin d, |C j|
  have hD (j : Fin d) : C j ≤ D := (le_abs_self _).trans
    (Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ j))
  have hholder : ∀ j, HolderBound (ball 0 1) (1 / 2)
      (fun x => (s • F (s • x)) j) D := by
    intro j
    obtain ⟨S, H, hS, hH, hSH, hs', hh'⟩ := hC j
    exact ⟨S, H, hS, hH, hSH.trans (hD j), hs', hh'⟩
  obtain ⟨v, hv, heq⟩ := exists_continuousOn_poisson_potential_of_gt h836 hd
    (fun x => u (s • x)) (fun x => s • g (s • x)) (fun x => s • F (s • x))
    (by simpa only [one_mul, one_smul] using hw')
    (by simpa only [smul_sub] using hJ')
    (measurable_const.smul (hFm.comp (continuous_const.smul continuous_id).measurable))
    (by simpa only [one_smul] using hu' 1 (by norm_num)) (hg' 1 (by norm_num)) D hholder
  obtain ⟨w, hwc, huw⟩ := exists_continuousOn_undilated_representative
    u v s (1 / 4) hs (by norm_num) hv heq
  have hsR : s * (1 / 4) = R := by dsimp [s]; ring
  rw [hsR] at hwc huw
  exact ⟨w, hwc, huw⟩

end EinsteinRelation.Correctors
