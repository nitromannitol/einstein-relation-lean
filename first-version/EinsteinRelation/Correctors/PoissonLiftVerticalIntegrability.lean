import EinsteinRelation.Correctors.PoissonLiftLocalIntegrability
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Regeneration.HalfSpaces

/-! Source: `paper/main.tex:735-739`. Local integrability of the
explicit height flux after normalizing the divergence source. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- A measurable source bounded by one gives a locally integrable
vertical flux for every locally integrable original gradient. -/
theorem locallyIntegrable_poissonLiftVertical {d : ℕ}
    (V : Vec d → Vec d) (hV : Measurable V)
    (hVn : ∀ x, euclideanNorm (V x) ≤ 1)
    (g : Vec d → Vec d) (hg : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (M : ℝ) :
    LocallyIntegrable (fun x =>
      (1 + euclideanSq (V x)) * M - dot (V x) (g x)) volume := by
  have hVc (i : Fin d) : Measurable (fun x => V x i) :=
    (measurable_pi_apply i).comp hV
  have hcoord (x : Vec d) (i : Fin d) : |V x i| ≤ 1 :=
    (Regeneration.coordinate_abs_le_euclideanNorm (V x) i).trans (hVn x)
  have hsq0 (x : Vec d) : 0 ≤ euclideanSq (V x) := by
    change 0 ≤ ∑ i, V x i * V x i
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (V x i))
  have hsq (x : Vec d) : euclideanSq (V x) ≤ 1 := by
    have h := Real.sq_sqrt (hsq0 x)
    have hn := hVn x
    change Real.sqrt (euclideanSq (V x)) ≤ 1 at hn
    nlinarith [Real.sqrt_nonneg (euclideanSq (V x))]
  have hVm : Measurable (fun x => euclideanSq (V x)) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ (fun i _ => (hVc i).mul (hVc i))
  have hfirst : LocallyIntegrable (fun x => (1 + euclideanSq (V x)) * M) volume := by
    apply (continuous_const.locallyIntegrable :
      LocallyIntegrable (fun _ : Vec d => 2 * |M|) volume).mono
      ((measurable_const.add hVm).mul measurable_const).aestronglyMeasurable
    apply ae_of_all
    intro x
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [abs_of_nonneg (by linarith [hsq0 x] : 0 ≤ 1 + euclideanSq (V x))]
    exact mul_le_mul_of_nonneg_right (by linarith [hsq x]) (abs_nonneg M)
  have hterms (i : Fin d) : LocallyIntegrable (fun x => V x i * g x i) volume := by
    apply (hg i).mono ((hVc i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable)
    apply ae_of_all
    intro x
    change |V x i * g x i| ≤ |g x i|
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (hcoord x i) (abs_nonneg (g x i))
  have hdot : LocallyIntegrable (fun x => dot (V x) (g x)) volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply integrable_finset_sum
    intro i _
    exact (hterms i).integrableOn_isCompact hK
  exact hfirst.sub hdot

end EinsteinRelation.Correctors
