import EinsteinRelation.Correctors.PoissonLiftWeakGradient
import EinsteinRelation.Correctors.PoissonLiftDivergence
import EinsteinRelation.Correctors.PoissonLiftVerticalIntegrability
import EinsteinRelation.Correctors.PoissonLiftLocalL2
import EinsteinRelation.Correctors.PoissonLiftCoefficient
import EinsteinRelation.Correctors.ClippedPoissonSource
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-! Source: `paper/main.tex:735-739`. The explicit augmented matrix and
potential solve the homogeneous weak equation on the lifted unit ball.
Only the original Poisson flux identity and a local source bound are used. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The original Poisson equation, encoded by `div (g-F)=0`, gives a
genuine homogeneous Sobolev solution with dimension-only ellipticity
after adjoining the height coordinate. -/
theorem weakSolution_poissonLift {d : ℕ}
    (u : Vec d → ℝ) (g F : Vec d → Vec d)
    (hw : HasWeakGradient Set.univ u g)
    (hJ : HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0))
    (hF : Measurable F) (M : ℝ) (hM : 0 < M)
    (hFn : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), euclideanNorm (F x) ≤ M)
    (hu : MemLp u 2 (volume.restrict (ball 0 1)))
    (hg : MemLp g 2 (volume.restrict (ball 0 1))) :
    WeakSolution (ball (0 : Vec (d + 1)) 1)
      (fun x => poissonLiftMatrix (clippedPoissonSource F M (poissonLiftBase x)))
      (poissonLiftPotential u M) (poissonLiftGradient g M) := by
  let V := clippedPoissonSource F M
  let B : Vec d → ℝ := fun x => (1 + euclideanSq (V x)) * M - dot (V x) (g x)
  have hV : Measurable V := measurable_clippedPoissonSource F hF M
  have hVn : ∀ x, euclideanNorm (V x) ≤ 1 := euclideanNorm_clippedPoissonSource_le F M hM
  have hB : LocallyIntegrable B volume := locallyIntegrable_poissonLiftVertical V hV hVn g
    (fun i => locallyIntegrableOn_univ.mp (hw i).2.1) M
  have hdiv := HasWeakDivergence.restrict_subset
    (Set.subset_univ (ball (0 : Vec (d + 1)) 1)) MeasurableSet.univ
    (hasWeakDivergence_poissonLiftFlux (fun x => g x - F x) B hJ hB)
  have hgrad := hasWeakGradient_poissonLift u g hw M
  obtain ⟨hul, hgl⟩ := memLp_poissonLift_potential_gradient u g M 1 (by norm_num) hu hg
  refine ⟨hul, hgl, fun i => HasWeakPartialDerivative.restrict_subset
    (Set.subset_univ _) MeasurableSet.univ (hgrad i), ?_⟩
  apply hdiv.congr_ae ?_ (ae_eq_refl _)
  have hb : MeasurableSet (ball (0 : Vec d) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hbl : MeasurableSet (ball (0 : Vec (d + 1)) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hbase : Measure.QuasiMeasurePreserving (poissonLiftBase : Vec (d + 1) → Vec d) volume volume :=
    Measure.quasiMeasurePreserving_snd.comp he.quasiMeasurePreserving
  have hcond := hbase.ae ((ae_restrict_iff' hb).mp hFn)
  filter_upwards [ae_restrict_of_ae hcond, ae_restrict_mem hbl] with x hx hxball
  have hxb : poissonLiftBase x ∈ ball (0 : Vec d) 1 := by
    change euclideanNorm (poissonLiftBase x - 0) < 1
    rw [sub_zero]
    exact (euclideanNorm_poissonLiftBase_le x).trans_lt (by
      simpa only [ball, sub_zero] using hxball)
  have hval : V (poissonLiftBase x) = M⁻¹ • F (poissonLiftBase x) :=
    if_pos (hx hxb)
  symm
  change (poissonLiftMatrix (V (poissonLiftBase x))).mulVec
      (Fin.cons M (g (poissonLiftBase x))) =
    Fin.cons (B (poissonLiftBase x)) (g (poissonLiftBase x) - F (poissonLiftBase x))
  dsimp only [B]
  rw [hval]
  exact poissonLiftMatrix_normalized_flux _ _ M hM.ne'

end EinsteinRelation.Correctors
